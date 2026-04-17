#lang racket

;; Dimoulas 2012 — randomized differential testing for the operational
;; 2012 CM model (model.rkt). Exercises the Redex <-> Lean <-> Typed-Racket
;; correspondence for evaluation, type inference, and contract inference.
;;
;; Mirrors Lean side:
;;   - ContractModels.Dimoulas2012.Executable.InferTypeProof
;;   - ContractModels.Dimoulas2012.Executable.Theorems

(require json
         racket/list
         racket/match
         racket/runtime-path
         rackunit
         redex/reduction-semantics
         "model.rkt")

(provide run-cm2012-random-checks!
         lean-run-batches
         query->lean-jsexpr
         lean-jsexpr->expr
         gen-expr
         random-label
         random-type)

(define-runtime-path model-dir ".")
;; model-dir is control-contract-model/dimoulas2012/; project root is two levels up.
(define project-root
  (simplify-path (build-path model-dir 'up 'up)))
(define lean-runner-source-path
  (simplify-path
   (build-path project-root "ContractModels" "Dimoulas2012" "Main" "Checker.lean")))
(define lean-runner-exec-source-path
  (simplify-path
   (build-path project-root "ContractModels" "Dimoulas2012" "Executable" "Semantics.lean")))
(define built-lean-runner-path
  (simplify-path (build-path project-root ".lake" "build" "bin" "dimoulas2012-checker")))

(define (built-runner-fresh?)
  (and (file-exists? built-lean-runner-path)
       (>= (file-or-directory-modify-seconds built-lean-runner-path)
           (max (file-or-directory-modify-seconds lean-runner-source-path)
                (file-or-directory-modify-seconds lean-runner-exec-source-path)))))

(define labels '("τ" "υ"))
(define observable-types
  '(Num Bool Unit
        (→ Num Num)
        (→ Bool Bool)
        (→ Num Bool)))

(define (lean-runner-available?)
  (or (built-runner-fresh?)
      (find-executable-path "lake")))

(define (lean-command)
  (if (built-runner-fresh?)
      (list (path->string built-lean-runner-path))
      (list (or (find-executable-path "lake") "lake")
            "env"
            "lean"
            "--run"
            (path->string lean-runner-source-path))))

(define (lean-run-batch queries #:timeout [timeout-seconds 30])
  (unless (lean-runner-available?)
    (error 'lean-run-batch "missing Lean CM2012 runner at ~a" built-lean-runner-path))
  (define request (hasheq 'fuel 200 'queries queries))
  (define-values (proc stdout stdin stderr)
    (parameterize ([current-directory project-root])
      (apply subprocess #f #f #f (lean-command))))
  (display (jsexpr->string request) stdin)
  (close-output-port stdin)
  (define done? (sync/timeout timeout-seconds proc))
  (unless done?
    (subprocess-kill proc #t)
    (error 'lean-run-batch "Lean CM2012 runner timed out after ~a seconds" timeout-seconds))
  (subprocess-wait proc)
  (define out (port->string stdout))
  (define err (port->string stderr))
  (unless (zero? (subprocess-status proc))
    (error 'lean-run-batch
           (string-append
            (format "Lean CM2012 runner failed with status ~a\n"
                    (subprocess-status proc))
            (if (string=? err "") "" (format "stderr:\n~a" err))
            (if (string=? out "") "" (format "stdout:\n~a" out)))))
  (define response (string->jsexpr out))
  (unless (list? response)
    (error 'lean-run-batch "expected JSON list from Lean, got ~s" response))
  response)

(define (chunk-list xs chunk-size)
  (let loop ([rest xs] [acc '()])
    (cond
      [(null? rest) (reverse acc)]
      [else
       (define-values (prefix suffix) (split-at rest (min chunk-size (length rest))))
       (loop suffix (cons prefix acc))])))

(define (lean-run-batches queries
                          #:timeout [timeout-seconds 30]
                          #:chunk-size [chunk-size 8])
  (append*
   (for/list ([chunk (in-list (chunk-list queries chunk-size))])
     (lean-run-batch chunk #:timeout timeout-seconds))))

(define (ty->lean-jsexpr ty)
  (match ty
    ['Num '("Num")]
    ['Bool '("Bool")]
    ['Unit '("Unit")]
    [`(→ ,t1 ,t2) `("->" ,(ty->lean-jsexpr t1) ,(ty->lean-jsexpr t2))]
    [`(Con ,t) `("Con" ,(ty->lean-jsexpr t))]
    [else (error 'ty->lean-jsexpr "unexpected type ~s" ty)]))

(define (lean-jsexpr->ty j)
  (match j
    ['null #f]
    [`("Num") 'Num]
    [`("Bool") 'Bool]
    [`("Unit") 'Unit]
    [`("->" ,t1 ,t2) `(→ ,(lean-jsexpr->ty t1) ,(lean-jsexpr->ty t2))]
    [`("Con" ,t) `(Con ,(lean-jsexpr->ty t))]
    [else (error 'lean-jsexpr->ty "unexpected Lean type ~s" j)]))

(define (lean-jsexpr->contract j)
  (match j
    [`("flat" ,e) `(flat ,(lean-jsexpr->expr e))]
    [`("flatAnnot" ,e ,ls) `(flatAnnot ,(lean-jsexpr->expr e) ,ls)]
    [`("arr" ,c1 ,c2)
     `(-> ,(lean-jsexpr->contract c1) ,(lean-jsexpr->contract c2))]
    [else
     (error 'lean-jsexpr->contract "unexpected Lean contract ~s" j)]))

(define (lean-jsexpr->expr j)
  (match j
    ['null #f]
    [`("var" ,x) (string->symbol x)]
    [`("int" ,n) n]
    [`("bool" ,b) b]
    [`("unit") 'unit]
    [`("lam" ,x ,t ,body)
     `(λ (,(string->symbol x) : ,(lean-jsexpr->ty t)) ,(lean-jsexpr->expr body))]
    [`("app" ,e1 ,e2)
     `(,(lean-jsexpr->expr e1) ,(lean-jsexpr->expr e2))]
    [`("if" ,e1 ,e2 ,e3)
     `(if ,(lean-jsexpr->expr e1)
          ,(lean-jsexpr->expr e2)
          ,(lean-jsexpr->expr e3))]
    [`("mu" ,x ,t ,body)
     `(μ (,(string->symbol x) : ,(lean-jsexpr->ty t)) ,(lean-jsexpr->expr body))]
    [`("unop" ,op ,e1)
     `(,(case op
          [("neg") '-]
          [("not") 'not]
          [("zero?") 'zero?]
          [("number?") 'number?]
          [("boolean?") 'boolean?]
          [("unit?") 'unit?]
          [else (error 'lean-jsexpr->expr "unknown unop ~s" op)])
       ,(lean-jsexpr->expr e1))]
    [`("monitor" ,k ,l ,j0 ,ctc ,e1)
     `(monitor ,(lean-jsexpr->contract ctc)
               ,(lean-jsexpr->expr e1)
               ,k ,l ,j0)]
    [`("check" ,k ,j0 ,e1 ,v)
     `(check ,(lean-jsexpr->expr e1)
             ,(lean-jsexpr->expr v)
             ,k ,j0)]
    [`("ctc-error" ,k ,j0) `(ctc-error ,k ,j0)]
    [`("own" ,e1 ,l) `(own ,(lean-jsexpr->expr e1) ,l)]
    [else
     (error 'lean-jsexpr->expr "unexpected Lean expr ~s" j)]))

(define (contract->lean-jsexpr c)
  (match c
    [`(flat ,e) `("flat" ,(expr->lean-jsexpr e))]
    [`(flatAnnot ,e ,ls) `("flatAnnot" ,(expr->lean-jsexpr e) ,ls)]
    [`(-> ,c1 ,c2) `("arr" ,(contract->lean-jsexpr c1) ,(contract->lean-jsexpr c2))]
    [else (error 'contract->lean-jsexpr "unexpected contract ~s" c)]))

(define (expr->lean-jsexpr e)
  (match e
    [(? integer?) `("int" ,e)]
    [(? boolean?) `("bool" ,e)]
    ['unit '("unit")]
    [(? symbol?) `("var" ,(symbol->string e))]
    [`(λ (,x : ,t) ,body)
     `("lam" ,(symbol->string x) ,(ty->lean-jsexpr t) ,(expr->lean-jsexpr body))]
    [`(if ,e1 ,e2 ,e3)
     `("if" ,(expr->lean-jsexpr e1) ,(expr->lean-jsexpr e2) ,(expr->lean-jsexpr e3))]
    [`(μ (,x : ,t) ,body)
     `("mu" ,(symbol->string x) ,(ty->lean-jsexpr t) ,(expr->lean-jsexpr body))]
    [`(,op ,e1)
     #:when (memq op '(- not zero? number? boolean? unit?))
     `("unop" ,(case op
                 [(-) "neg"]
                 [(not) "not"]
                 [(zero?) "zero?"]
                 [(number?) "number?"]
                 [(boolean?) "boolean?"]
                 [(unit?) "unit?"])
               ,(expr->lean-jsexpr e1))]
    [`(,e1 ,e2)
     `("app" ,(expr->lean-jsexpr e1) ,(expr->lean-jsexpr e2))]
    [`(monitor ,ctc ,e1 ,k ,l ,j)
     `("monitor" ,k ,l ,j ,(contract->lean-jsexpr ctc) ,(expr->lean-jsexpr e1))]
    [`(check ,e1 ,v ,k ,j)
     `("check" ,k ,j ,(expr->lean-jsexpr e1) ,(expr->lean-jsexpr v))]
    [`(ctc-error ,k ,j) `("ctc-error" ,k ,j)]
    [`(own ,e1 ,l) `("own" ,(expr->lean-jsexpr e1) ,l)]
    [else (error 'expr->lean-jsexpr "unexpected expression ~s" e)]))

(define (lean-answer->answer j)
  (match j
    [`("int" ,n) `(int ,n)]
    [`("bool" ,b) `(bool ,b)]
    [`("unit") '(unit)]
    [`("procedure") '(procedure)]
    [`("ctc-error" ,k ,j) `(ctc-error ,k ,j)]
    [`("timeout") '(timeout)]
    [`("stuck") '(stuck)]
    [else (error 'lean-answer->answer "unexpected Lean answer ~s" j)]))

(define (normalize-answer v)
  (match v
    ['timeout '(timeout)]
    [(? integer?) `(int ,v)]
    [(? boolean?) `(bool ,v)]
    ['unit '(unit)]
    [`(λ . ,_) '(procedure)]
    [`(own ,inner ,_) (normalize-answer inner)]
    [`(ctc-error ,k ,j) `(ctc-error ,k ,j)]
    [_ '(stuck)]))

(define (top-tag e)
  (match e
    [`(if . ,_) 'if]
    [`(μ . ,_) 'mu]
    [`(monitor ,(and ctc `(flat . ,_)) . ,_) 'monitor-flat]
    [`(monitor ,(and ctc `(flatAnnot . ,_)) . ,_) 'monitor-flatAnnot]
    [`(monitor ,(and ctc `(-> . ,_)) . ,_) 'monitor-arr]
    [`(λ . ,_) 'lam]
    [`(,e1 ,e2) 'app]
    [`(,op ,_) #:when (memq op '(- not zero? number? boolean? unit?)) 'unop]
    [(? integer?) 'int]
    [(? boolean?) 'bool]
    ['unit 'unit]
    [_ 'other]))

(define (flat-predicate-body base-type x)
  (match base-type
    ['Num `(number? ,x)]
    ['Bool `(boolean? ,x)]
    ['Unit `(unit? ,x)]
    [else `(number? ,x)]))

(define (vars-of-type env t)
  (for/list ([binding (in-list env)]
             #:when (equal? (cdr binding) t))
    (car binding)))

(define (fresh-name stem env)
  (gensym stem))

(define (default-expr env t)
  (match t
    ['Num (match (vars-of-type env 'Num)
            [(list x _ ...) x]
            [_ 0])]
    ['Bool (match (vars-of-type env 'Bool)
             [(list x _ ...) x]
             [_ #f])]
    ['Unit (match (vars-of-type env 'Unit)
             [(list x _ ...) x]
             [_ 'unit])]
    [`(→ ,t1 ,t2)
     (match (vars-of-type env t)
       [(list x _ ...) x]
       [_ (define x (fresh-name 'x env))
          `(λ (,x : ,t1) ,(default-expr (cons (cons x t1) env) t2))])]
    [else 0]))

(define (random-type)
  (list-ref observable-types (random (length observable-types))))

(define (random-label)
  (list-ref labels (random (length labels))))

(define (gen-contract fuel ks ls j t)
  (match t
    ['Num
     (define x (fresh-name 'c '()))
     (define pred `(λ (,x : Num) ,(flat-predicate-body 'Num x)))
     (if (zero? (random 2))
         `(flat ,pred)
         `(flatAnnot (own ,pred ,j) ,ks))]
    ['Bool
     (define x (fresh-name 'c '()))
     (define pred `(λ (,x : Bool) ,(flat-predicate-body 'Bool x)))
     (if (zero? (random 2))
         `(flat ,pred)
         `(flatAnnot (own ,pred ,j) ,ks))]
    ['Unit
     (define x (fresh-name 'c '()))
     (define pred `(λ (,x : Unit) ,(flat-predicate-body 'Unit x)))
     (if (zero? (random 2))
         `(flat ,pred)
         `(flatAnnot (own ,pred ,j) ,ks))]
    [`(→ ,t1 ,t2)
     `(-> ,(gen-contract fuel ls ks j t1)
          ,(gen-contract fuel ks ls j t2))]
    [else (error 'gen-contract "unexpected target type ~s" t)]))

(define (gen-expr fuel env l t)
  (define fallback (λ () (default-expr env t)))
  (define var-choices
    (for/list ([x (in-list (vars-of-type env t))])
      (λ () x)))
  (define (literal-choices)
    (match t
      ['Num (list (λ () (- (random 11) 5)))]
      ['Bool (list (λ () (zero? (random 2))))]
      ['Unit (list (λ () 'unit))]
      [`(→ ,t1 ,t2)
       (list (λ ()
               (define x (fresh-name 'x env))
               `(λ (,x : ,t1)
                  ,(gen-expr 0 (cons (cons x t1) env) l t2))))]
      [_ '()]))
  (define (generic-choices smaller)
    (list
     (λ ()
       `(if ,(gen-expr smaller env l 'Bool)
            ,(gen-expr smaller env l t)
            ,(gen-expr smaller env l t)))
     (λ ()
       (define dom (random-type))
       `(,(gen-expr smaller env l `(→ ,dom ,t))
         ,(gen-expr smaller env l dom)))
     (λ ()
       (define x (fresh-name 'μ env))
       `(μ (,x : ,t)
           ,(gen-expr smaller (cons (cons x t) env) l t)))
     (λ ()
       (define k (random-label))
       (define inner (gen-expr 0 '() k t))
       (define c (gen-contract 0 (list k) (list l) "j" t))
       `(monitor ,c (own ,inner ,k) ,k ,l "j"))))
  (define (type-specific-choices smaller)
    (match t
      ['Num
       (list (λ () `(- ,(gen-expr smaller env l 'Num))))]
      ['Bool
       (list (λ () `(not ,(gen-expr smaller env l 'Bool)))
             (λ () `(zero? ,(gen-expr smaller env l 'Num)))
             (λ () `(number? ,(gen-expr smaller env l (random-type))))
             (λ () `(boolean? ,(gen-expr smaller env l (random-type))))
             (λ () `(unit? ,(gen-expr smaller env l (random-type)))))]
      [`(→ ,t1 ,t2)
       (list (λ ()
               (define x (fresh-name 'x env))
               `(λ (,x : ,t1)
                  ,(gen-expr smaller (cons (cons x t1) env) l t2))))]
      [_ '()]))
  (define choices
    (append var-choices
            (literal-choices)
            (if (zero? fuel)
                '()
                (append (generic-choices (sub1 fuel))
                        (type-specific-choices (sub1 fuel))))))
  ((if (null? choices)
       fallback
       (list-ref choices (random (length choices))))))

(define (cm2012-types e)
  (judgment-holds (cm2012-tc · ,e t) t))

(define (increment-count counts key)
  (hash-update counts key add1 0))

(define (query->lean-jsexpr expr l)
  (hasheq 'expr (expr->lean-jsexpr expr)
          'sourceLabel l))

(define (check-sample! expected-type expr l lean-result)
  (define redex-types (cm2012-types expr))
  (unless (member expected-type redex-types equal?)
    (error 'check-sample!
           "Redex rejected generated term\nexpected: ~s\nredex types: ~s\nterm:\n~s"
           expected-type redex-types expr))
  (define lean-initial (lean-jsexpr->ty (hash-ref lean-result 'initialType)))
  (unless (equal? lean-initial expected-type)
    (error 'check-sample!
           "Lean initial type mismatch\nexpected: ~s\nlean: ~s\nterm:\n~s"
           expected-type lean-initial expr))
  (define redex-answer (normalize-answer (cm2012-eval/answer expr #:fuel 200)))
  (define lean-answer (lean-answer->answer (hash-ref lean-result 'answer)))
  (unless (equal? redex-answer lean-answer)
    (error 'check-sample!
           "Redex/Lean answer mismatch\nredex: ~s\nlean: ~s\nterm:\n~s"
           redex-answer lean-answer expr))
  (unless (hash-ref lean-result 'wfSource)
    (error 'check-sample! "Lean wfSource rejected generated term\nterm:\n~s" expr))
  (unless (hash-ref lean-result 'preservesType)
    (error 'check-sample! "Lean preservation approximation failed\nterm:\n~s" expr)))

(define (run-cm2012-random-checks! #:samples [samples 8]
                                   #:seed [seed 20260321]
                                   #:expr-fuel [expr-fuel 3]
                                   #:chunk-size [chunk-size 8]
                                   #:timeout [timeout-seconds 30]
                                   #:verbose? [verbose? #t])
  (random-seed seed)
  (define samples*
    (for/list ([i (in-range samples)])
      (define l (random-label))
      (define t (random-type))
      (list l t (gen-expr expr-fuel '() l t))))
  (define coverage
    (for/fold ([counts (hash)]) ([sample (in-list samples*)])
      (increment-count counts (top-tag (third sample)))))
  (define lean-results
    (lean-run-batches
     (for/list ([sample (in-list samples*)])
       (match-define (list l t expr) sample)
       (query->lean-jsexpr expr l))
     #:chunk-size chunk-size
     #:timeout timeout-seconds))
  (for ([sample (in-list samples*)]
        [lean-result (in-list lean-results)])
    (match-define (list l t expr) sample)
    (check-sample! t expr l lean-result))
  (when verbose?
    (printf "cm2012 redex/lean checks passed\n")
    (printf "seed: ~a\n" seed)
    (printf "samples: ~a\n" samples)
    (printf "expr fuel: ~a\n" expr-fuel)
    (printf "chunk size: ~a\n" chunk-size)
    (printf "coverage: ~s\n" (sort (hash->list coverage) symbol<? #:key car))))

(module+ test
  ;; Keep the smoke test small. Larger CM2012 cross-checks are practical,
  ;; but the Redex side gets expensive quickly at `expr-fuel` 4.
  (run-cm2012-random-checks! #:samples 8
                             #:expr-fuel 3
                             #:verbose? #f))

(module+ main
  (run-cm2012-random-checks!))
