#lang racket

;; Takikawa 2013 — randomized differential testing for the 2013 model.
;;
;; Exercises the Redex <-> Lean <-> Typed-Racket correspondence for
;; evaluation (`redex-eval/answer`) and for the paper's mixed-language
;; soundness / complete-monitoring properties.
;;
;; Lean counterpart: Takikawa2013.Theorems, Takikawa2013.InterpreterTheorems.

(require racket/contract
         json
         racket/list
         racket/match
         racket/pretty
         racket/runtime-path
         racket/string
         rackunit
         redex/reduction-semantics
         (except-in "model.rkt" let)
         "random-soundness.rkt")

(provide redex-eval/answer
         racket-eval/answer
         lean-eval/answer
         (struct-out campaign)
         (struct-out prepared-sample)
         default-main-campaigns
         default-test-campaigns
         build-evaluation-samples
         compare-term!
         run-random-checks!
         run-random-suite!)

;; Evaluate translated terms in this module's namespace so helpers like
;; `lookup-store` and `raise-model-blame` are available to `eval`.
(define-namespace-anchor anchor)

(define current-runtime-store
  (make-parameter (hash)))

(define-runtime-path model-dir ".")
(define project-root
  (simplify-path (build-path model-dir 'up 'up)))
(define lean-main-path
  (simplify-path (build-path project-root "ContractModels" "Takikawa2013" "Main" "Interpreter.lean")))
(define built-lean-runner-path
  (simplify-path (build-path project-root ".lake" "build" "bin" "takikawa2013-interpreter")))

(define no-lean-answer
  (gensym 'no-lean-answer))

(struct prepared-sample (label term store core-term) #:transparent)

(define (lookup-store name)
  (hash-ref (current-runtime-store)
            name
            (λ ()
              (error 'lookup-store "missing runtime binding for ~s" name))))

(define (raise-model-blame positive-name contract-name)
  (contract
   (rename-contract
    (flat-named-contract contract-name (λ (_) #f))
    contract-name)
   0
   positive-name
   "unobservable"))

(define (store-kind-from-name name)
  (define s (symbol->string name))
  (cond
    [(string-prefix? s "tag") 'Prompt]
    [(string-prefix? s "key") 'Mark]
    [else
     (error 'store-kind-from-name
            "cannot infer store kind for ~s"
            name)]))

(define (store-name->id name kind)
  (define s (symbol->string name))
  (define prefix
    (case kind
      [(Prompt) "tag"]
      [(Mark) "key"]
      [else
       (error 'store-name->id "unexpected store kind ~s for ~s" kind name)]))
  (cond
    [(equal? s prefix) 0]
    [else
     (define m
       (regexp-match (pregexp (format "^~a([0-9]+)$" prefix)) s))
     (unless m
       (error 'store-name->id
              "cannot extract numeric id from ~s"
              name))
     (string->number (cadr m))]))

(define (store->bindings σ)
  (match σ
    ['· '()]
    [`(,name : ,t ,rest)
     (cons (cons name t) (store->bindings rest))]
    [`(,name ,rest)
     (cons (cons name (store-kind-from-name name))
           (store->bindings rest))]
    [else
     (error 'store->bindings "unexpected store ~s" σ)]))

(define (make-runtime-store σ)
  (for/hash ([binding (in-list (store->bindings σ))])
    (match-define (cons name t) binding)
    (values
     name
     (match t
       ['Prompt
        (make-continuation-prompt-tag name)]
       ['Mark
        (make-continuation-mark-key)]
       [`(Prompt ,_ ,_)
        (make-continuation-prompt-tag name)]
       [`(Mark ,_)
        (make-continuation-mark-key)]
       [else
        (error 'make-runtime-store
               "cannot realize store binding ~s : ~s"
               name
               t)]))))

(define (store->lean-symbol-table σ)
  (for/hash ([binding (in-list (store->bindings σ))])
    (match-define (cons name t) binding)
    (values name t)))

(define default-lean-runner-command
  (if (file-exists? built-lean-runner-path)
      (list (path->string built-lean-runner-path))
      (list (or (find-executable-path "lake") "lake")
            "env"
            "lean"
            "--run"
            (path->string lean-main-path))))

(define (lean-runner-command)
  (if (getenv "TSTH_LEAN_INTERPRETER")
      (list (getenv "TSTH_LEAN_INTERPRETER"))
      default-lean-runner-command))

(define (lean-runner-description)
  (string-join (map ~a (lean-runner-command)) " "))

(define (lean-interpreter-available?)
  (or (getenv "TSTH_LEAN_INTERPRETER")
      (find-executable-path "lake")))

(define (ty->lean-jsexpr t)
  (match t
    ['Num '("Num")]
    ['String '("String")]
    ['Bool '("Bool")]
    ['Unit '("Unit")]
    [`(→ ,t1 ,t2)
     `("->" ,(ty->lean-jsexpr t1) ,(ty->lean-jsexpr t2))]
    [`(Prompt ,t1 ,t2)
     `("Prompt" ,(ty->lean-jsexpr t1) ,(ty->lean-jsexpr t2))]
    [`(Mark ,t0)
     `("Mark" ,(ty->lean-jsexpr t0))]
    [`(List ,t0)
     `("List" ,(ty->lean-jsexpr t0))]
    [`(Con ,t0)
     `("Con" ,(ty->lean-jsexpr t0))]
    [else
     (error 'ty->lean-jsexpr "unexpected type ~s" t)]))

(define (contract->lean-jsexpr ctc store-table)
  (match ctc
    [`(flat ,pred)
     `("flat" ,(expr->lean-jsexpr pred store-table))]
    [`(-> ,ctc-a ,ctc-r)
     `("arr"
       ,(contract->lean-jsexpr ctc-a store-table)
       ,(contract->lean-jsexpr ctc-r store-table))]
    [`(prompt-tag/c ,ctc-abort ,ctc-call/comp ,_t1 ,_t2)
     `("prompt-tag/c"
       ,(contract->lean-jsexpr ctc-abort store-table)
       ,(contract->lean-jsexpr ctc-call/comp store-table))]
    [`(mark/c ,inner ,_t)
     `("mark/c" ,(contract->lean-jsexpr inner store-table))]
    [`(list/c ,inner)
     `("list/c" ,(contract->lean-jsexpr inner store-table))]
    [`(flatAnnot ,pred ,labels)
     `("flatAnnot" ,(expr->lean-jsexpr pred store-table) ,labels)]
    [else
     (error 'contract->lean-jsexpr "unexpected contract ~s" ctc)]))

(define (mark-frame->lean-jsexpr w store-table)
  (for/list ([frame (in-list w)])
    (match frame
      [`(,mk ,v)
       (list (expr->lean-jsexpr mk store-table)
             (expr->lean-jsexpr v store-table))]
      [else
       (error 'mark-frame->lean-jsexpr "unexpected frame ~s" frame)])))

(define (symbol->lean-expr x store-table)
  (cond
    [(hash-has-key? store-table x)
     (define raw-kind (hash-ref store-table x))
     (define kind
       (match raw-kind
         ['Prompt 'Prompt]
         ['Mark 'Mark]
         [`(Prompt ,_ ,_) 'Prompt]
         [`(Mark ,_) 'Mark]
         [else
          (error 'symbol->lean-expr
                 "unexpected store binding type ~s for ~s"
                 raw-kind
                 x)]))
     (define id (store-name->id x kind))
     (case kind
       [(Prompt) `("tag" ,id)]
       [(Mark) `("key" ,id)])]
    [(eq? x 'call/comp)
     '("callCompVal")]
    [(eq? x 'call/cm)
     '("callCmVal")]
    [else
     `("var" ,(symbol->string x))]))

(define (expr->lean-jsexpr e store-table)
  (match e
    [(? number?) `("int" ,e)]
    [(? boolean?) `("bool" ,e)]
    [(? string?) `("string" ,e)]
    ['unit '("unit")]
    [(? symbol?) (symbol->lean-expr e store-table)]
    [`(λ (,x : ,t0) ,body)
     `("lam" ,(symbol->string x) ,(ty->lean-jsexpr t0)
              ,(expr->lean-jsexpr body store-table))]
    [`(μ (,x : ,t0) ,body)
     `("mu" ,(symbol->string x) ,(ty->lean-jsexpr t0)
             ,(expr->lean-jsexpr body store-table))]
    [`(if ,e1 ,e2 ,e3)
     `("if"
       ,(expr->lean-jsexpr e1 store-table)
       ,(expr->lean-jsexpr e2 store-table)
       ,(expr->lean-jsexpr e3 store-table))]
    [`(,op ,e1 ,e2)
     #:when (memq op '(+ - *))
     `("binop"
       ,(symbol->string op)
       ,(expr->lean-jsexpr e1 store-table)
       ,(expr->lean-jsexpr e2 store-table))]
    [`(,op ,e1)
     #:when (memq op '(- not zero? number? unit? boolean? procedure? prompt-tag?))
     `("unop" ,(symbol->string op) ,(expr->lean-jsexpr e1 store-table))]
    [`(cons ,e1 ,e2)
     `("cons"
       ,(expr->lean-jsexpr e1 store-table)
       ,(expr->lean-jsexpr e2 store-table))]
    [`(null ,t0)
     `("null" ,(ty->lean-jsexpr t0))]
    [`(case ,scrutinee
        (null = ,null-branch)
        ((cons ,x1 ,x2) = ,cons-branch))
     `("case"
       ,(expr->lean-jsexpr scrutinee store-table)
       ,(expr->lean-jsexpr null-branch store-table)
       ,(symbol->string x1)
       ,(symbol->string x2)
       ,(expr->lean-jsexpr cons-branch store-table))]
    [`(make-prompt-tag ,t1 ,t2)
     `("make-prompt-tag" ,(ty->lean-jsexpr t1) ,(ty->lean-jsexpr t2))]
    [`(make-cm-key ,t0)
     `("make-cm-key" ,(ty->lean-jsexpr t0))]
    [`(% ,e1 ,e2 ,vh)
     `("prompt"
       ,(expr->lean-jsexpr e1 store-table)
       ,(expr->lean-jsexpr e2 store-table)
       ,(expr->lean-jsexpr vh store-table))]
    [`(abort ,t0 ,pt ,v)
     `("abort"
       ,(ty->lean-jsexpr t0)
       ,(expr->lean-jsexpr pt store-table)
       ,(expr->lean-jsexpr v store-table))]
    [`(wcm ,w ,body)
     `("wcm"
       ,(mark-frame->lean-jsexpr w store-table)
       ,(expr->lean-jsexpr body store-table))]
    [`(ccm ,e1 ,t0)
     `("ccm" ,(expr->lean-jsexpr e1 store-table) ,(ty->lean-jsexpr t0))]
    [`(call/comp ,e1 ,e2)
     `("call/comp"
       ,(expr->lean-jsexpr e1 store-table)
       ,(expr->lean-jsexpr e2 store-table))]
    [`(call/cm ,e1 ,e2 ,e3)
     `("call/cm"
       ,(expr->lean-jsexpr e1 store-table)
       ,(expr->lean-jsexpr e2 store-table)
       ,(expr->lean-jsexpr e3 store-table))]
    [`(update ,e1 ,e2 ,e3)
     `("update"
       ,(expr->lean-jsexpr e1 store-table)
       ,(expr->lean-jsexpr e2 store-table)
       ,(expr->lean-jsexpr e3 store-table))]
    [`(monitor ,ctc ,e1 ,k ,l ,j)
     `("monitor"
       ,k
       ,l
       ,j
       ,(contract->lean-jsexpr ctc store-table)
       ,(expr->lean-jsexpr e1 store-table))]
    [`(PG ,ctc1 ,ctc2 ,pt ,k ,l ,j)
     `("PG"
       ,k
       ,l
       ,j
       ,(contract->lean-jsexpr ctc1 store-table)
       ,(contract->lean-jsexpr ctc2 store-table)
       ,(expr->lean-jsexpr pt store-table))]
    [`(MG ,ctc ,mk ,k ,l ,j)
     `("MG"
       ,k
       ,l
       ,j
       ,(contract->lean-jsexpr ctc store-table)
       ,(expr->lean-jsexpr mk store-table))]
    [`(ctc-error ,k ,j)
     `("ctc-error" ,k ,j)]
    ['(error)
     '("error")]
    [`(check ,e1 ,v ,l ,j)
     `("check"
       ,l
       ,j
       ,(expr->lean-jsexpr e1 store-table)
       ,(expr->lean-jsexpr v store-table))]
    [`(own ,e1 ,l)
     `("own" ,(expr->lean-jsexpr e1 store-table) ,l)]
    [`(,e1 ,e2)
     `("app"
       ,(expr->lean-jsexpr e1 store-table)
       ,(expr->lean-jsexpr e2 store-table))]
    [else
     (error 'expr->lean-jsexpr "unexpected expression ~s" e)]))

(define (store->lean-jsexpr σ)
  (define bindings (store->bindings σ))
  (define tags
    (for/list ([binding (in-list bindings)]
               #:when (match (cdr binding)
                        ['Prompt #t]
                        [`(Prompt ,_ ,_) #t]
                        [_ #f]))
      (store-name->id (car binding) 'Prompt)))
  (define keys
    (for/list ([binding (in-list bindings)]
               #:when (match (cdr binding)
                        ['Mark #t]
                        [`(Mark ,_) #t]
                        [_ #f]))
      (store-name->id (car binding) 'Mark)))
  (hasheq 'tags tags
          'keys keys))

(define (program->lean-jsexpr core-term store)
  (define store-table (store->lean-symbol-table store))
  (hasheq 'expr (expr->lean-jsexpr core-term store-table)
          'store (store->lean-jsexpr store)))

(define (lean-jsexpr->answer jsexpr)
  (match jsexpr
    [`("int" ,n) n]
    [`("bool" ,b) b]
    [`("string" ,s) s]
    ['("unit") 'unit]
    [`("list" ,xs)
     (map lean-jsexpr->answer xs)]
    ['("prompt-tag") 'prompt-tag]
    ['("mark-key") 'mark-key]
    ['("procedure") 'procedure]
    ['("contract") 'contract]
    [`("ctc-error" ,k ,j) `(ctc-error ,k ,j)]
    ['("error") 'error]
    ['("missing-prompt") 'missing-prompt]
    ['("stuck") 'stuck]
    ['("non-terminating") 'non-terminating]
    [else
     (error 'lean-jsexpr->answer "unexpected Lean answer ~s" jsexpr)]))

(define (chunk-list xs size)
  (unless (positive? size)
    (error 'chunk-list "batch size must be positive, got ~s" size))
  (let loop ([rest xs]
             [chunks '()])
    (cond
      [(null? rest) (reverse chunks)]
      [else
       (define n (min size (length rest)))
       (define-values (front tail) (split-at rest n))
       (loop tail (cons front chunks))])))

(define (lean-run-batch programs
                        #:fuel [fuel 2000]
                        #:timeout [timeout-seconds 5])
  (unless (lean-interpreter-available?)
    (error 'lean-run-batch
           "Lean interpreter runner unavailable: ~a"
           (lean-runner-description)))
  (define request
    (hasheq 'fuel fuel
            'programs programs))
  (define cmd (lean-runner-command))
  (define-values (proc stdout stdin stderr)
    (parameterize ([current-directory project-root])
      (apply subprocess
             #f
             #f
             #f
             cmd)))
  (display (jsexpr->string request) stdin)
  (close-output-port stdin)
  (define done? (sync/timeout timeout-seconds proc))
  (unless done?
    (subprocess-kill proc #t)
    (error 'lean-run-batch
           "Lean interpreter timed out after ~a seconds"
           timeout-seconds))
  (subprocess-wait proc)
  (define out (port->string stdout))
  (define err (port->string stderr))
  (unless (zero? (subprocess-status proc))
    (error 'lean-run-batch
           (string-append
            (format "Lean interpreter failed with status ~a\n"
                    (subprocess-status proc))
            (if (string=? err "")
                ""
                (format "stderr:\n~a" err))
            (if (string=? out "")
                ""
                (format "stdout:\n~a" out)))))
  (define response (string->jsexpr out))
  (unless (list? response)
    (error 'lean-run-batch "expected JSON list from Lean, got ~s" response))
  response)

(define (lean-eval/answers prepared-samples
                           #:fuel [fuel 2000]
                           #:timeout [timeout-seconds 5]
                           #:batch-size [batch-size 50])
  (append-map
   (λ (chunk)
     (define programs
       (for/list ([sample (in-list chunk)])
         (program->lean-jsexpr (prepared-sample-core-term sample)
                               (prepared-sample-store sample))))
     (map lean-jsexpr->answer
          (lean-run-batch programs
                          #:fuel fuel
                          #:timeout timeout-seconds)))
   (chunk-list prepared-samples batch-size)))

(define (lean-eval/answer t
                          #:init-store [store '·]
                          #:fuel [fuel 2000]
                          #:timeout [timeout-seconds 5])
  (define sample
    (prepare-sample 'lean-single t store))
  (car (lean-eval/answers (list sample)
                          #:fuel fuel
                          #:timeout timeout-seconds)))

(define (timeout-call thunk timeout-seconds)
  (define ch (make-channel))
  (define worker
    (thread
     (λ ()
       (channel-put ch
                    (with-handlers ([exn? values])
                      (thunk))))))
  (define result (sync/timeout timeout-seconds ch))
  (cond
    [result
     (when (thread-running? worker)
       (kill-thread worker))
     (if (exn? result)
         (raise result)
         result)]
    [else
     (kill-thread worker)
     'non-terminating]))

(define (extract-ctc-error e)
  (define blame (exn:fail:contract:blame-object e))
  `(ctc-error ,(format "~a" (blame-positive blame))
              ,(format "~a" (blame-contract blame))))

(define (runtime-list->answer lst)
  (map runtime-value->answer lst))

(define (runtime-value->answer v)
  (cond
    [(number? v) v]
    [(boolean? v) v]
    [(string? v) v]
    [(void? v) 'unit]
    [(null? v) '()]
    [(list? v) (runtime-list->answer v)]
    [(continuation-prompt-tag? v) 'prompt-tag]
    [(continuation-mark-key? v) 'mark-key]
    [(procedure? v) 'procedure]
    [(contract? v) 'contract]
    [else
     (error 'runtime-value->answer "unexpected Racket result ~e" v)]))

(define (ctc->racket ctc store)
  (match ctc
    [`(flat ,pred)
     `(flat-contract ,(redex->racket pred store))]
    [`(-> ,ctc-a ,ctc-r)
     `(-> ,(ctc->racket ctc-a store)
          ,(ctc->racket ctc-r store))]
    [`(prompt-tag/c ,ctc-abort ,ctc-call/cc ,_t1 ,_t2)
     `(prompt-tag/c ,(ctc->racket ctc-abort store)
                    #:call/cc
                    ,(ctc->racket ctc-call/cc store))]
    [`(mark/c ,inner ,_t)
     `(continuation-mark-key/c ,(ctc->racket inner store))]
    [`(list/c ,inner)
     `(listof ,(ctc->racket inner store))]
    [else
     (error 'ctc->racket "unexpected contract ~s" ctc)]))

(define (wrap-monitor ctc value positive negative contract-name)
  `(contract
    (rename-contract ,ctc ,contract-name)
    ,value
    ,positive
    ,negative))

(define (wcm->racket w body store)
  (match w
    ['() body]
    [`((,mk ,v) ,rest ...)
     `(with-continuation-mark
        ,(redex->racket mk store)
        ,(redex->racket v store)
        ,(wcm->racket rest body store))]
    [else
     (error 'wcm->racket "unexpected mark frame ~s" w)]))

(define (mu-lambda-body? e)
  (match e
    [`(λ (,x : ,_t) ,body)
     (and (not (eq? x #f))
          (translatable? body))]
    [_ #f]))

(define (translatable? e)
  (match e
    [(? number?) #t]
    [(? boolean?) #t]
    [(? string?) #t]
    ['unit #t]
    [(? symbol?) #t]
    [`(λ (,x : ,_t) ,body)
     (translatable? body)]
    [`(μ (,x : ,_t) ,body)
     (mu-lambda-body? body)]
    [`(if ,e1 ,e2 ,e3)
     (and (translatable? e1)
          (translatable? e2)
          (translatable? e3))]
    [`(,op ,e1 ,e2)
     #:when (memq op '(+ - *))
     (and (translatable? e1)
          (translatable? e2))]
    [`(,op ,e1)
     #:when (memq op '(- not zero? number? unit? boolean? procedure? prompt-tag?))
     (translatable? e1)]
    [`(cons ,e1 ,e2)
     (and (translatable? e1)
          (translatable? e2))]
    [`(null ,_t) #t]
    [`(case ,e1 (null = ,e2) ((cons ,x1 ,x2) = ,e3))
     (and (translatable? e1)
          (translatable? e2)
          (translatable? e3))]
    [`(let ([(,x : ,_t) ,e1]) ,e2)
     (and (translatable? e1)
          (translatable? e2))]
    [`(make-prompt-tag ,_t1 ,_t2) #t]
    [`(make-cm-key ,_t) #t]
    [`(% ,e1 ,e2 ,v)
     (and (translatable? e1)
          (translatable? e2)
          (translatable? v))]
    [`(abort ,_t ,e1 ,e2)
     (and (translatable? e1)
          (translatable? e2))]
    [`(wcm ,w ,body)
     (and (andmap (λ (frame)
                    (match frame
                      [`(,mk ,v)
                       (and (translatable? mk)
                            (translatable? v))]
                      [_ #f]))
                  w)
          (translatable? body))]
    [`(ccm ,e1 ,_t)
     (translatable? e1)]
    [`(call/comp ,e1 ,e2)
     (and (translatable? e1)
          (translatable? e2))]
    [`(call/cm ,e1 ,e2 ,e3)
     (and (translatable? e1)
          (translatable? e2)
          (translatable? e3))]
    [`(monitor ,ctc ,e1 ,_k ,_l ,_j)
     (and (translatable? ctc)
          (translatable? e1))]
    [`(PG ,ctc1 ,ctc2 ,pt ,_k ,_l ,_j)
     (and (translatable? ctc1)
          (translatable? ctc2)
          (translatable? pt))]
    [`(MG ,ctc ,mk ,_k ,_l ,_j)
     (and (translatable? ctc)
          (translatable? mk))]
    [`(flat ,pred)
     (translatable? pred)]
    [`(prompt-tag/c ,ctc1 ,ctc2 ,_t1 ,_t2)
     (and (translatable? ctc1)
          (translatable? ctc2))]
    [`(mark/c ,ctc ,_t)
     (translatable? ctc)]
    [`(list/c ,ctc)
     (translatable? ctc)]
    [`(-> ,ctc1 ,ctc2)
     (and (translatable? ctc1)
          (translatable? ctc2))]
    [`(,e1 ,e2)
     (and (translatable? e1)
          (translatable? e2))]
    ['(error) #t]
    [`(ctc-error ,_k ,_j) #t]
    [_ #f]))

(define (redex->racket e [store (hash)])
  (match e
    [(? number?) e]
    [(? boolean?) e]
    [(? string?) e]
    ['unit '(void)]
    [(? symbol?)
     (if (hash-has-key? store e)
         `(lookup-store ',e)
         e)]
    [`(λ (,x : ,_t) ,body)
     `(lambda (,x) ,(redex->racket body store))]
    [`(μ (,x : ,_t) (λ (,arg : ,arg-t) ,body))
     `(letrec ([,x (lambda (,arg) ,(redex->racket body store))])
        ,x)]
    [`(if ,e1 ,e2 ,e3)
     `(if ,(redex->racket e1 store)
          ,(redex->racket e2 store)
          ,(redex->racket e3 store))]
    [`(,op ,e1 ,e2)
     #:when (memq op '(+ - *))
     `(,op ,(redex->racket e1 store)
           ,(redex->racket e2 store))]
    [`(,op ,e1)
     #:when (memq op '(- not zero? number? boolean? procedure?))
     `(,op ,(redex->racket e1 store))]
    [`(unit? ,e1)
     `(void? ,(redex->racket e1 store))]
    [`(prompt-tag? ,e1)
     `(continuation-prompt-tag? ,(redex->racket e1 store))]
    [`(cons ,e1 ,e2)
     `(cons ,(redex->racket e1 store)
            ,(redex->racket e2 store))]
    [`(null ,_t)
     ''()]
    [`(let ([(,x : ,_t) ,e1]) ,e2)
     `((lambda (,x) ,(redex->racket e2 store))
       ,(redex->racket e1 store))]
    [`(case ,scrutinee
        (null = ,null-branch)
        ((cons ,x1 ,x2) = ,cons-branch))
     (define tmp (gensym 'lst))
     `(let ([,tmp ,(redex->racket scrutinee store)])
        (if (null? ,tmp)
            ,(redex->racket null-branch store)
            (let ([,x1 (car ,tmp)]
                  [,x2 (cdr ,tmp)])
              ,(redex->racket cons-branch store))))]
    [`(make-prompt-tag ,_t1 ,_t2)
     '(make-continuation-prompt-tag)]
    [`(make-cm-key ,_t)
     '(make-continuation-mark-key)]
    [`(% ,e1 ,e2 ,v)
     `(call-with-continuation-prompt
       (lambda () ,(redex->racket e1 store))
       ,(redex->racket e2 store)
       ,(redex->racket v store))]
    [`(abort ,_t ,e1 ,e2)
     `(abort-current-continuation
       ,(redex->racket e1 store)
       ,(redex->racket e2 store))]
    [`(wcm ,w ,body)
     (wcm->racket w (redex->racket body store) store)]
    [`(ccm ,e1 ,_t)
     `(continuation-mark-set->list
       (current-continuation-marks)
       ,(redex->racket e1 store))]
    [`(call/comp ,e1 ,e2)
     `(call-with-composable-continuation
       ,(redex->racket e1 store)
       ,(redex->racket e2 store))]
    [`(call/cm ,e1 ,e2 ,e3)
     `(with-continuation-mark
        ,(redex->racket e1 store)
        ,(redex->racket e2 store)
        ,(redex->racket e3 store))]
    [`(monitor ,ctc ,e1 ,k ,l ,j)
     (wrap-monitor (ctc->racket ctc store)
                   (redex->racket e1 store)
                   k
                   l
                   j)]
    [`(PG ,ctc1 ,ctc2 ,pt ,k ,l ,j)
     (wrap-monitor (ctc->racket `(prompt-tag/c ,ctc1 ,ctc2 Unit Unit) store)
                   (redex->racket pt store)
                   k
                   l
                   j)]
    [`(MG ,ctc ,mk ,k ,l ,j)
     (wrap-monitor (ctc->racket `(mark/c ,ctc Unit) store)
                   (redex->racket mk store)
                   k
                   l
                   j)]
    [`(ctc-error ,k ,j)
     `(raise-model-blame ,k ,j)]
    ['(error)
     `(error 'abort-model "error")]
    [`(,e1 ,e2)
     `(,(redex->racket e1 store)
       ,(redex->racket e2 store))]
    [else
     (error 'redex->racket "unexpected term ~s" e)]))

(define (racket-eval/answer t
                            #:init-store [store '·]
                            #:timeout [timeout-seconds 0.5])
  (define runtime-store (make-runtime-store store))
  (define ns (namespace-anchor->namespace anchor))
  (timeout-call
   (λ ()
     (with-handlers ([exn:fail:contract:blame? extract-ctc-error]
                     [exn:fail?
                      (λ (e)
                        (if (regexp-match? #rx"no corresponding prompt"
                                           (exn-message e))
                            'missing-prompt
                            'error))])
       (parameterize ([current-namespace ns]
                      [current-runtime-store runtime-store])
         (runtime-value->answer
          (eval (redex->racket t runtime-store))))))
   timeout-seconds))

(define (redex-list->answer v)
  (match v
    [`(null ,_t) '()]
    [`(cons ,a ,d)
     (cons (redex-value->answer a)
           (redex-list->answer d))]
    [else
     (error 'redex-list->answer "expected a proper Redex list, got ~s" v)]))

(define (redex-value->answer v)
  (match v
    [(? number?) v]
    [(? boolean?) v]
    [(? string?) v]
    ['unit 'unit]
    [`(null ,_t) '()]
    [`(cons ,_ ,_)
     (redex-list->answer v)]
    ['key 'mark-key]
    [`(MG ,_ ...) 'mark-key]
    ['tag 'prompt-tag]
    [`(PG ,_ ...) 'prompt-tag]
    [`(λ ,_ ...) 'procedure]
    [`(-> ,_ ,_) 'contract]
    [`(prompt-tag/c ,_ ...) 'contract]
    [`(mark/c ,_ ...) 'contract]
    [`(list/c ,_ ...) 'contract]
    [`(flat ,_) 'procedure]
    [`(ctc-error ,k ,j) `(ctc-error ,k ,j)]
    ['(error) 'error]
    [else
     (error 'redex-value->answer "unexpected Redex result ~s" v)]))

(define (e-missing-prompt? e)
  (or (redex-match abort-lang
                   (side-condition
                    (in-hole E_pt (call/comp v pt))
                    (term (no-match E_pt pt)))
                   e)
      (redex-match abort-lang
                   (side-condition
                    (in-hole E_pt (abort t pt v))
                    (term (no-match E_pt pt)))
                   e)))

(define (redex-eval/answer t
                           #:init-store [store '·]
                           #:step-limit [step-limit 1000]
                           #:timeout [timeout-seconds 0.5])
  (timeout-call
   (λ ()
     (define state (term (<> ,t ,store)))
     (define steps 0)
     (define exceeded? #f)
     (define results
       (apply-reduction-relation*
        abort-red
        state
        #:stop-when
        (λ (_)
          (set! steps (add1 steps))
          (and (> steps step-limit)
               (set! exceeded? #t)))))
     (cond
       [(or exceeded? (empty? results))
        'non-terminating]
       [else
        (define result (cadr (car results)))
        (with-handlers ([exn:fail?
                         (λ (_)
                           (if (e-missing-prompt? result)
                               'missing-prompt
                               (raise-user-error
                                'redex-eval/answer
                                (format "unexpected Redex result ~s" result))))])
          (redex-value->answer result))]))
   timeout-seconds))

(define (term->string t)
  (with-output-to-string
    (λ ()
      (pretty-write t))))

(define (desugar-term t)
  (match t
    [(? number?) t]
    [(? boolean?) t]
    [(? string?) t]
    ['unit 'unit]
    [(? symbol?) t]
    [`(λ (,x : ,ty) ,body)
     `(λ (,x : ,ty) ,(desugar-term body))]
    [`(μ (,x : ,ty) ,body)
     `(μ (,x : ,ty) ,(desugar-term body))]
    [`(if ,e1 ,e2 ,e3)
     `(if ,(desugar-term e1)
          ,(desugar-term e2)
          ,(desugar-term e3))]
    [`(let ([(,x : ,ty) ,e1]) ,e2)
     `((λ (,x : ,ty) ,(desugar-term e2))
       ,(desugar-term e1))]
    [`(,op ,e1 ,e2)
     #:when (memq op '(+ - * cons))
     `(,op ,(desugar-term e1)
           ,(desugar-term e2))]
    [`(,op ,e1)
     #:when (memq op '(- not zero? number? unit? boolean? procedure? prompt-tag? flat list/c))
     `(,op ,(desugar-term e1))]
    [`(null ,_t)
     t]
    [`(case ,e1 (null = ,e2) ((cons ,x1 ,x2) = ,e3))
     `(case ,(desugar-term e1)
        (null = ,(desugar-term e2))
        ((cons ,x1 ,x2) = ,(desugar-term e3)))]
    [`(make-prompt-tag ,_t1 ,_t2)
     t]
    [`(make-cm-key ,_t)
     t]
    [`(% ,e1 ,e2 ,v)
     `(% ,(desugar-term e1)
         ,(desugar-term e2)
         ,(desugar-term v))]
    [`(abort ,t0 ,e1 ,e2)
     `(abort ,t0
             ,(desugar-term e1)
             ,(desugar-term e2))]
    [`(wcm ,w ,body)
     `(wcm ,(for/list ([frame (in-list w)])
              (match frame
                [`(,mk ,v)
                 `(,(desugar-term mk) ,(desugar-term v))]))
           ,(desugar-term body))]
    [`(ccm ,e1 ,t0)
     `(ccm ,(desugar-term e1) ,t0)]
    [`(call/comp ,e1 ,e2)
     `(call/comp ,(desugar-term e1) ,(desugar-term e2))]
    [`(call/cm ,e1 ,e2 ,e3)
     `(call/cm ,(desugar-term e1)
               ,(desugar-term e2)
               ,(desugar-term e3))]
    [`(monitor ,ctc ,e1 ,k ,l ,j)
     `(monitor ,(desugar-term ctc)
               ,(desugar-term e1)
               ,k
               ,l
               ,j)]
    [`(PG ,ctc1 ,ctc2 ,pt ,k ,l ,j)
     `(PG ,(desugar-term ctc1)
          ,(desugar-term ctc2)
          ,(desugar-term pt)
          ,k
          ,l
          ,j)]
    [`(MG ,ctc ,mk ,k ,l ,j)
     `(MG ,(desugar-term ctc)
          ,(desugar-term mk)
          ,k
          ,l
          ,j)]
    [`(prompt-tag/c ,ctc1 ,ctc2 ,t1 ,t2)
     `(prompt-tag/c ,(desugar-term ctc1)
                    ,(desugar-term ctc2)
                    ,t1
                    ,t2)]
    [`(mark/c ,ctc ,t0)
     `(mark/c ,(desugar-term ctc) ,t0)]
    [`(-> ,ctc1 ,ctc2)
     `(-> ,(desugar-term ctc1) ,(desugar-term ctc2))]
    [`(ctc-error ,_k ,_j)
     t]
    ['(error)
     t]
    [`(,e1 ,e2)
     `(,(desugar-term e1)
       ,(desugar-term e2))]
    [_
     (error 'desugar-term "unexpected term ~s" t)]))

(define (prepare-sample label term store)
  (define core-term (desugar-term term))
  (unless (translatable? core-term)
    (error 'prepare-sample
           "~a produced an unsupported term:\n~a"
           label
           (term->string term)))
  (prepared-sample label term store core-term))

(define (compare-prepared-sample! sample
                                  #:redex-step-limit [redex-step-limit 1000]
                                  #:redex-timeout [redex-timeout-seconds 0.5]
                                  #:racket-timeout [racket-timeout-seconds 0.5]
                                  #:check-lean? [check-lean? (lean-interpreter-available?)]
                                  #:lean-answer [lean-answer no-lean-answer]
                                  #:lean-fuel [lean-fuel 2000]
                                  #:lean-timeout [lean-timeout-seconds 5])
  (define label (prepared-sample-label sample))
  (define term (prepared-sample-term sample))
  (define store (prepared-sample-store sample))
  (define core-term (prepared-sample-core-term sample))
  (define redex-answer
    (redex-eval/answer core-term
                       #:init-store store
                       #:step-limit redex-step-limit
                       #:timeout redex-timeout-seconds))
  (define racket-answer
    (racket-eval/answer core-term
                        #:init-store store
                        #:timeout racket-timeout-seconds))
  (unless (equal? redex-answer racket-answer)
    (error 'compare-prepared-sample!
           (string-append
            (format "~a mismatch\n" label)
            (format "redex: ~s\n" redex-answer)
            (format "racket: ~s\n" racket-answer)
            "term:\n"
            (term->string term)
            "store:\n"
            (term->string store))))
  (when check-lean?
    (define actual-lean-answer
      (if (eq? lean-answer no-lean-answer)
          (lean-eval/answer core-term
                            #:init-store store
                            #:fuel lean-fuel
                            #:timeout lean-timeout-seconds)
          lean-answer))
    (unless (equal? redex-answer actual-lean-answer)
      (error 'compare-prepared-sample!
             (string-append
              (format "~a mismatch\n" label)
              (format "redex: ~s\n" redex-answer)
              (format "lean: ~s\n" actual-lean-answer)
              "term:\n"
              (term->string term)
              "store:\n"
              (term->string store)))))
  redex-answer)

(define (compare-term! term
                       #:label [label 'sample]
                       #:init-store [store '·]
                       #:redex-step-limit [redex-step-limit 1000]
                       #:redex-timeout [redex-timeout-seconds 0.5]
                       #:racket-timeout [racket-timeout-seconds 0.5]
                       #:check-lean? [check-lean? (lean-interpreter-available?)]
                       #:lean-answer [lean-answer no-lean-answer]
                       #:lean-fuel [lean-fuel 2000]
                       #:lean-timeout [lean-timeout-seconds 5])
  (compare-prepared-sample! (prepare-sample label term store)
                            #:redex-step-limit redex-step-limit
                            #:redex-timeout redex-timeout-seconds
                            #:racket-timeout racket-timeout-seconds
                            #:check-lean? check-lean?
                            #:lean-answer lean-answer
                            #:lean-fuel lean-fuel
                            #:lean-timeout lean-timeout-seconds))

(define interesting-constructs
  '(monitor
    prompt-tag/c
    mark/c
    list/c
    ->
    case
    %
    abort
    call/comp
    call/cm
    ccm
    wcm
    make-prompt-tag
    make-cm-key))

(define (walk-term t f)
  (f t)
  (match t
    [`(λ (,x : ,ty) ,body)
     (walk-term body f)]
    [`(μ (,x : ,ty) ,body)
     (walk-term body f)]
    [`(if ,e1 ,e2 ,e3)
     (walk-term e1 f)
     (walk-term e2 f)
     (walk-term e3 f)]
    [`(,e1 ,e2)
     (walk-term e1 f)
     (walk-term e2 f)]
    [`(,op ,e1 ,e2)
     #:when (memq op '(+ - * cons))
     (walk-term e1 f)
     (walk-term e2 f)]
    [`(,op ,e1)
     #:when (memq op '(- not zero? number? unit? boolean? procedure? prompt-tag?))
     (walk-term e1 f)]
    [`(case ,e1 (null = ,e2) ((cons ,x1 ,x2) = ,e3))
     (walk-term e1 f)
     (walk-term e2 f)
     (walk-term e3 f)]
    [`(% ,e1 ,e2 ,v)
     (walk-term e1 f)
     (walk-term e2 f)
     (walk-term v f)]
    [`(abort ,_t ,e1 ,e2)
     (walk-term e1 f)
     (walk-term e2 f)]
    [`(wcm ,w ,body)
     (for ([frame (in-list w)])
       (match frame
         [`(,mk ,v)
          (walk-term mk f)
          (walk-term v f)]))
     (walk-term body f)]
    [`(ccm ,e1 ,_t)
     (walk-term e1 f)]
    [`(call/comp ,e1 ,e2)
     (walk-term e1 f)
     (walk-term e2 f)]
    [`(call/cm ,e1 ,e2 ,e3)
     (walk-term e1 f)
     (walk-term e2 f)
     (walk-term e3 f)]
    [`(monitor ,ctc ,e1 ,_k ,_l ,_j)
     (walk-term ctc f)
     (walk-term e1 f)]
    [`(PG ,ctc1 ,ctc2 ,pt ,_k ,_l ,_j)
     (walk-term ctc1 f)
     (walk-term ctc2 f)
     (walk-term pt f)]
    [`(MG ,ctc ,mk ,_k ,_l ,_j)
     (walk-term ctc f)
     (walk-term mk f)]
    [`(flat ,pred)
     (walk-term pred f)]
    [`(-> ,ctc1 ,ctc2)
     (walk-term ctc1 f)
     (walk-term ctc2 f)]
    [`(prompt-tag/c ,ctc1 ,ctc2 ,_t1 ,_t2)
     (walk-term ctc1 f)
     (walk-term ctc2 f)]
    [`(mark/c ,ctc ,_t)
     (walk-term ctc f)]
    [`(list/c ,ctc)
     (walk-term ctc f)]
    [_ (void)]))

(define (update-coverage! coverage t)
  (walk-term
   t
   (λ (subterm)
     (match subterm
       [`(,head . ,_)
        (when (memq head interesting-constructs)
          (hash-update! coverage head add1 0))]
       [_ (void)]))))

(define labels
  '("server" "client" "con" "A" "B" "C" "left" "right" "pos" "neg"))

(define (random-label)
  (list-ref labels (random (length labels))))

(define (random-small-int)
  (- (random 7) 3))

(define (random-nonzero-small-int)
  (let loop ()
    (define n (random-small-int))
    (if (zero? n)
        (loop)
        n)))

(define (zero?-contract)
  '(flat (λ (x : Num) (zero? x))))

(define (number?-contract)
  '(flat (λ (x : Num) (number? x))))

(define (zero->number-contract)
  `(-> ,(zero?-contract) ,(number?-contract)))

(define (number->number-contract)
  `(-> ,(number?-contract) ,(number?-contract)))

(define (number->zero-contract)
  `(-> ,(number?-contract) ,(zero?-contract)))

(define (redex-list xs)
  (for/fold ([tail '(null Num)])
            ([x (in-list (reverse xs))])
    `(cons ,x ,tail)))

(define (fresh-blame-triple)
  (list (random-label) (random-label) (random-label)))

(define (gen-random-abort-term)
  (define n (random-small-int))
  (define k1 (random-small-int))
  (define k2 (random-small-int))
  (case (random 3)
    [(0)
     `((λ (pt : (Prompt Num Num))
         (% (abort Num pt ,n)
            pt
            (λ (x : Num) (+ x ,k1))))
       (make-prompt-tag Num Num))]
    [(1)
     `((λ (pt : (Prompt Num Num))
         (% (% (abort Num pt ,n)
               (make-prompt-tag Num Num)
               (λ (x : Num) (+ x ,k2)))
            pt
            (λ (x : Num) (+ x ,k1))))
       (make-prompt-tag Num Num))]
    [else
     `((λ (pt : (Prompt Num Num))
         (% (% (abort Num pt ,n)
               pt
               (λ (x : Num) (+ x ,k2)))
            pt
            (λ (x : Num) (+ x ,k1))))
       (make-prompt-tag Num Num))]))

(define (gen-random-call/comp-term)
  (define base (random-small-int))
  (define a (random-small-int))
  (define b (random-small-int))
  `((λ (pt : (Prompt Num Num))
      (% (+ ,base
            (call/comp
             (λ (kont : (→ Num Num))
               (+ (kont ,a) (kont ,b)))
             pt))
         pt
         (λ (x : Num) x)))
    (make-prompt-tag Num Num)))

(define (gen-random-mark-term)
  (define v1 (random-small-int))
  (define v2 (random-small-int))
  (if (zero? (random 2))
      `((λ (mk : (Mark Num))
          (call/cm mk ,v1 (ccm mk Num)))
        (make-cm-key Num))
      `((λ (mk : (Mark Num))
          (call/cm
           mk
           ,v1
           (call/cm mk ,v2 (ccm mk Num))))
        (make-cm-key Num))))

(define (gen-random-wcm-term)
  (define outer (random-small-int))
  (define inner (random-small-int))
  (vector
   `((λ (f : (→ Unit (List Num)))
       (wcm ((key0 ,outer)) (f unit)))
     (λ (x : Unit)
       (wcm ((key0 ,inner)) (ccm key0 Num))))
   '(key0 ·)))

(define (gen-random-mark-contract-term)
  (define value (if (zero? (random 2)) 0 (max 1 (abs (random-small-int)))))
  (define blame (fresh-blame-triple))
  (match-define (list pos neg con) blame)
  `((λ (mk : (Mark Num))
      (call/cm mk ,value (ccm mk Num)))
    (monitor (mark/c ,(zero?-contract) Num)
             (make-cm-key Num)
             ,pos
             ,neg
             ,con)))

(define (gen-random-flat-contract-term)
  (define blame (fresh-blame-triple))
  (match-define (list pos neg con) blame)
  (define good? (zero? (random 2)))
  `(monitor ,(if good? (number?-contract) (zero?-contract))
            ,(if good? (random-small-int) (max 1 (abs (random-small-int))))
            ,pos
            ,neg
            ,con))

(define (gen-random-function-contract-term)
  (define blame (fresh-blame-triple))
  (match-define (list pos neg con) blame)
  (case (random 3)
    [(0)
     `((monitor (-> ,(zero?-contract) ,(number?-contract))
                (λ (x : Num) (+ x ,(random-small-int)))
                ,pos
                ,neg
                ,con)
       0)]
    [(1)
     `((monitor (-> ,(zero?-contract) ,(number?-contract))
                (λ (x : Num) (+ x ,(random-small-int)))
                ,pos
                ,neg
                ,con)
       ,(max 1 (abs (random-small-int))))]
    [else
     `((monitor (-> ,(number?-contract) ,(zero?-contract))
                (λ (x : Num) (+ x 1))
                ,pos
                ,neg
                ,con)
       ,(random-small-int))]))

(define (gen-random-list-contract-term)
  (define blame (fresh-blame-triple))
  (match-define (list pos neg con) blame)
  (define good? (zero? (random 2)))
  (define len (+ 1 (random 3)))
  (define xs
    (for/list ([i (in-range len)])
      (if (and (not good?) (= i (random len)))
          (max 1 (abs (random-small-int)))
          0)))
  `(monitor (list/c ,(zero?-contract))
            ,(redex-list xs)
            ,pos
            ,neg
            ,con))

(define (gen-random-prompt-tag-abort-term)
  (define blame (fresh-blame-triple))
  (match-define (list pos neg con) blame)
  (define value (if (zero? (random 2)) 0 (max 1 (abs (random-small-int)))))
  `((λ (pt : (Prompt Num Num))
      (% (abort Num pt ,value)
         pt
         (λ (x : Num) (+ x 1))))
    (monitor (prompt-tag/c ,(zero?-contract) ,(number?-contract) Num Num)
             (make-prompt-tag Num Num)
             ,pos
             ,neg
             ,con)))

(define (gen-random-prompt-tag-call/comp-term)
  (define blame (fresh-blame-triple))
  (match-define (list pos neg con) blame)
  `((λ (pt : (Prompt Num Num))
      (% (+ 1
            (call/comp
             (λ (kont : (→ Num Num))
               (kont 0))
             pt))
         pt
         (λ (x : Num) (+ x 1))))
    (monitor (prompt-tag/c ,(zero?-contract) ,(zero?-contract) Num Num)
             (make-prompt-tag Num Num)
             ,pos
             ,neg
             ,con)))

(define (gen-random-ho-prompt-tag-abort-term)
  (define blame (fresh-blame-triple))
  (match-define (list pos neg con) blame)
  (define mode (random 3))
  (define ctc
    (case mode
      [(0) (number->number-contract)]
      [(1) (number->zero-contract)]
      [else (zero->number-contract)]))
  (define handler-arg
    (if (= mode 2)
        (random-nonzero-small-int)
        (random-small-int)))
  (define body
    (case mode
      [(0) `(λ (x : Num) (+ x ,(random-small-int)))]
      [(1) `(λ (x : Num) ,(random-nonzero-small-int))]
      [else `(λ (x : Num) (+ x ,(random-small-int)))]))
  `((λ (pt : (Prompt (→ Num Num) Num))
      (% (abort Num pt ,body)
         pt
         (λ (f : (→ Num Num)) (f ,handler-arg))))
    (monitor (prompt-tag/c ,ctc ,(number?-contract) (→ Num Num) Num)
             (make-prompt-tag (→ Num Num) Num)
             ,pos
             ,neg
             ,con)))

(define (gen-random-prompt-flow-term)
  (define blame (fresh-blame-triple))
  (match-define (list pos neg con) blame)
  (define mode (random 3))
  (define ctc
    (case mode
      [(0) (number->number-contract)]
      [(1) (number->zero-contract)]
      [else (zero->number-contract)]))
  (define apply-arg
    (if (= mode 2)
        (random-nonzero-small-int)
        (random-small-int)))
  (define body
    (case mode
      [(0) `(λ (v : Num) (+ v ,(random-small-int)))]
      [(1) `(λ (v : Num) ,(random-nonzero-small-int))]
      [else `(λ (v : Num) (+ v ,(random-small-int)))]))
  `(let ([(do-prompt : (→ (→ (Prompt (→ Num Num) Num) Num) Num))
          (let ([(pt : (Prompt (→ Num Num) Num))
                 (make-prompt-tag (→ Num Num) Num)])
            (monitor
             (-> (-> (prompt-tag/c ,ctc
                                   ,(number?-contract)
                                   (→ Num Num)
                                   Num)
                      ,(number?-contract))
                 ,(number?-contract))
             (λ (f : (→ (Prompt (→ Num Num) Num) Num))
               (% (f pt)
                  pt
                  (λ (f : (→ Num Num)) (f ,apply-arg))))
             ,pos
             ,neg
             ,con))])
      (do-prompt
       (λ (pt : (Prompt (→ Num Num) Num))
         (abort Num pt ,body)))))

(define (gen-random-double-prompt-flow-term)
  (define blame1 (fresh-blame-triple))
  (define blame2 (fresh-blame-triple))
  (match-define (list pos1 neg1 con1) blame1)
  (match-define (list pos2 neg2 con2) blame2)
  (define mode (random 3))
  (define ctc1
    (case mode
      [(0) (number->number-contract)]
      [(1) (number->number-contract)]
      [else (number->zero-contract)]))
  (define ctc2
    (case mode
      [(0) (number->number-contract)]
      [(1) (zero->number-contract)]
      [else (number->number-contract)]))
  (define apply-arg
    (if (= mode 1)
        (random-nonzero-small-int)
        (random-small-int)))
  (define body
    (if (= mode 2)
        `(λ (v : Num) ,(random-nonzero-small-int))
        `(λ (v : Num) (+ v ,(random-small-int)))))
  `(let ([(do-prompt : (→ (→ (Prompt (→ Num Num) Num) Num) Num))
          (let ([(pt : (Prompt (→ Num Num) Num))
                 (make-prompt-tag (→ Num Num) Num)])
            (monitor
             (-> (-> (prompt-tag/c ,ctc1
                                   ,(number?-contract)
                                   (→ Num Num)
                                   Num)
                      ,(number?-contract))
                 ,(number?-contract))
             (λ (f : (→ (Prompt (→ Num Num) Num) Num))
               (% (f pt)
                  pt
                  (λ (f : (→ Num Num)) (f ,apply-arg))))
             ,pos1
             ,neg1
             ,con1))])
      (let ([(do-prompt-2 : (→ (→ (Prompt (→ Num Num) Num) Num) Num))
             (monitor
              (-> (-> (prompt-tag/c ,ctc2
                                    ,(number?-contract)
                                    (→ Num Num)
                                    Num)
                       ,(number?-contract))
                  ,(number?-contract))
              (λ (f : (→ (Prompt (→ Num Num) Num) Num))
                (do-prompt f))
              ,pos2
              ,neg2
              ,con2)])
        (do-prompt-2
         (λ (pt : (Prompt (→ Num Num) Num))
           (abort Num pt ,body))))))

(define (gen-random-ho-list-contract-term)
  (define blame (fresh-blame-triple))
  (match-define (list pos neg con) blame)
  (define mode (random 3))
  (define ctc
    (case mode
      [(0) (number->number-contract)]
      [(1) (number->zero-contract)]
      [else (zero->number-contract)]))
  (define arg
    (if (= mode 2)
        (random-nonzero-small-int)
        (random-small-int)))
  (define fn
    (case mode
      [(0) `(λ (x : Num) (+ x ,(random-small-int)))]
      [(1) `(λ (x : Num) ,(random-nonzero-small-int))]
      [else `(λ (x : Num) (+ x ,(random-small-int)))]))
  `((λ (fs : (List (→ Num Num)))
      (case fs
        (null = 0)
        ((cons f rest) = (f ,arg))))
    (monitor (list/c ,ctc)
             (cons ,fn (null (→ Num Num)))
             ,pos
             ,neg
             ,con)))

(define (gen-random-call/comp-mark-term)
  (define outer (random-small-int))
  (define inner (random-small-int))
  (define base (random-small-int))
  `((λ (pt : (Prompt Num Num))
      ((λ (mk : (Mark Num))
         (% (call/cm
             mk
             ,outer
             (+ (call/comp
                 (λ (k : (→ Num Num))
                   (call/cm mk ,inner (k ,base)))
                 pt)
                (case (ccm mk Num)
                  (null = 0)
                  ((cons x xs) = x))))
            pt
            (λ (x : Num) x)))
       (make-cm-key Num)))
    (make-prompt-tag Num Num)))

(struct campaign (name count generator) #:transparent)

(define deterministic-samples
  (list
   (list 'list-contract
         '(monitor (list/c (flat (λ (x : Num) (zero? x))))
                   (cons 0 (cons 6 (null Num)))
                   "pos"
                   "neg"
                   "con")
         '·)
   (list 'abort-basic
         '((λ (pt : (Prompt Num Num))
             (% (abort Num pt 5)
                pt
                (λ (x : Num) (+ x 1))))
           (make-prompt-tag Num Num))
         '·)
   (list 'abort-past
         '((λ (pt : (Prompt Num Num))
             (% (% (abort Num pt 5)
                   (make-prompt-tag Num Num)
                   (λ (x : Num) (+ x 2)))
                pt
                (λ (x : Num) (+ x 1))))
           (make-prompt-tag Num Num))
         '·)
   (list 'abort-innermost
         '((λ (pt : (Prompt Num Num))
             (% (% (abort Num pt 5)
                   pt
                   (λ (x : Num) (+ x 2)))
                pt
                (λ (x : Num) (+ x 1))))
           (make-prompt-tag Num Num))
         '·)
   (list 'call-comp
         '((λ (pt : (Prompt Num Num))
             (% (+ 1
                   (call/comp
                    (λ (kont : (→ Num Num))
                      (+ (kont 3) (kont 5)))
                    pt))
                pt
                (λ (x : Num) x)))
           (make-prompt-tag Num Num))
         '·)
   (list 'mark-basic
         '((λ (mk : (Mark Num))
             (call/cm mk 5 (ccm mk Num)))
           (make-cm-key Num))
         '·)
   (list 'mark-contract
         '((λ (mk : (Mark Num))
             (call/cm mk 5 (ccm mk Num)))
           (monitor (mark/c (flat (λ (x : Num) (zero? x))) Num)
                    (make-cm-key Num)
                    "pos"
                    "neg"
                    "con"))
         '·)
   (list 'prompt-tag-contract
         '((λ (pt : (Prompt Num Num))
             (% (abort Num pt 3)
                pt
                (λ (x : Num) (+ x 1))))
           (monitor (prompt-tag/c
                     (flat (λ (x : Num) (zero? x)))
                     (flat (λ (x : Num) (zero? x)))
                     Num
                     Num)
                    (make-prompt-tag Num Num)
                    "server"
                    "client"
                    "con"))
         '·)
   (list 'store-merge
         '((λ (f : (→ Unit (List Num)))
             (wcm ((key0 5)) (f unit)))
           (λ (x : Unit)
             (wcm ((key0 3)) (ccm key0 Num))))
         '(key0 ·))))

(define default-main-campaigns
  (list
   (campaign 'abort 250 gen-random-abort-term)
   (campaign 'call/comp 250 gen-random-call/comp-term)
   (campaign 'marks 250 gen-random-mark-term)
   (campaign 'wcm 100 gen-random-wcm-term)
   (campaign 'mark/c 200 gen-random-mark-contract-term)
   (campaign 'flat-contract 200 gen-random-flat-contract-term)
   (campaign 'arrow-contract 200 gen-random-function-contract-term)
   (campaign 'list-contract 200 gen-random-list-contract-term)
   (campaign 'list-contract/ho 150 gen-random-ho-list-contract-term)
   (campaign 'prompt-tag/abort 200 gen-random-prompt-tag-abort-term)
   (campaign 'prompt-tag/call/comp 200 gen-random-prompt-tag-call/comp-term)
   (campaign 'prompt-tag/abort-ho 150 gen-random-ho-prompt-tag-abort-term)
   (campaign 'prompt-flow 150 gen-random-prompt-flow-term)
   (campaign 'prompt-flow/double 125 gen-random-double-prompt-flow-term)
   (campaign 'call/comp+marks 150 gen-random-call/comp-mark-term)))

(define default-test-campaigns
  (list
   (campaign 'abort 25 gen-random-abort-term)
   (campaign 'call/comp 25 gen-random-call/comp-term)
   (campaign 'marks 25 gen-random-mark-term)
   (campaign 'wcm 10 gen-random-wcm-term)
   (campaign 'mark/c 20 gen-random-mark-contract-term)
   (campaign 'flat-contract 20 gen-random-flat-contract-term)
   (campaign 'arrow-contract 20 gen-random-function-contract-term)
   (campaign 'list-contract 20 gen-random-list-contract-term)
   (campaign 'list-contract/ho 15 gen-random-ho-list-contract-term)
   (campaign 'prompt-tag/abort 20 gen-random-prompt-tag-abort-term)
   (campaign 'prompt-tag/call/comp 20 gen-random-prompt-tag-call/comp-term)
   (campaign 'prompt-tag/abort-ho 15 gen-random-ho-prompt-tag-abort-term)
   (campaign 'prompt-flow 15 gen-random-prompt-flow-term)
   (campaign 'prompt-flow/double 10 gen-random-double-prompt-flow-term)
   (campaign 'call/comp+marks 15 gen-random-call/comp-mark-term)))

(define (collect-deterministic-samples)
  (for/list ([entry (in-list deterministic-samples)])
    (match-define (list label term store) entry)
    (prepare-sample label term store)))

(define (collect-campaign-sample-batch camp start end)
  (for/list ([i (in-range start end)])
    (define sample ((campaign-generator camp)))
    (define-values (term store)
      (match sample
        [(vector term store)
         (values term store)]
        [term
         (values term '·)]))
    (prepare-sample (format "~a/~a" (campaign-name camp) i)
                    term
                    store)))

(define (build-evaluation-samples #:campaigns [campaigns default-main-campaigns]
                                  #:seed [seed 20260320]
                                  #:verbose? [verbose? #f])
  (random-seed seed)
  (append
   (collect-deterministic-samples)
   (append*
    (for/list ([camp (in-list campaigns)])
      (when verbose?
        (printf "collecting campaign ~a: ~a samples\n"
                (campaign-name camp)
                (campaign-count camp)))
      (collect-campaign-sample-batch camp 0 (campaign-count camp))))))

(define (compare-prepared-samples! prepared-samples
                                   coverage
                                   #:check-lean? [check-lean? (lean-interpreter-available?)]
                                   #:lean-fuel [lean-fuel 2000]
                                   #:lean-timeout [lean-timeout 5]
                                   #:lean-batch-size [lean-batch-size 50]
                                   #:redex-step-limit [redex-step-limit 1000]
                                   #:redex-timeout [redex-timeout 0.5]
                                   #:racket-timeout [racket-timeout 0.5])
  (unless (null? prepared-samples)
    (define lean-answers
      (and check-lean?
           (lean-eval/answers prepared-samples
                              #:fuel lean-fuel
                              #:timeout lean-timeout
                              #:batch-size lean-batch-size)))
    (for ([sample (in-list prepared-samples)]
          [lean-answer (in-list (if check-lean?
                                    lean-answers
                                    (make-list (length prepared-samples)
                                               no-lean-answer)))])
      (compare-prepared-sample!
       sample
       #:redex-step-limit redex-step-limit
       #:redex-timeout redex-timeout
       #:racket-timeout racket-timeout
       #:check-lean? check-lean?
       #:lean-answer lean-answer
       #:lean-fuel lean-fuel
       #:lean-timeout lean-timeout)
      (update-coverage! coverage (prepared-sample-term sample)))))

(define (coverage-summary coverage)
  (for/list ([name (in-list interesting-constructs)])
    (list name (hash-ref coverage name 0))))

(define (run-random-checks! #:campaigns [campaigns default-main-campaigns]
                            #:seed [seed 20260320]
                            #:verbose? [verbose? #t]
                            #:with-lean? [with-lean? (lean-interpreter-available?)]
                            #:lean-fuel [lean-fuel 2000]
                            #:lean-timeout [lean-timeout 5]
                            #:lean-batch-size [lean-batch-size 50]
                            #:sample-batch-size [sample-batch-size 200]
                            #:redex-step-limit [redex-step-limit 1000]
                            #:redex-timeout [redex-timeout 0.5]
                            #:racket-timeout [racket-timeout 0.5])
  (random-seed seed)
  (unless (positive? sample-batch-size)
    (error 'run-random-checks!
           "sample batch size must be positive, got ~s"
           sample-batch-size))
  (define coverage (make-hash))
  (define start (current-inexact-milliseconds))
  (compare-prepared-samples! (collect-deterministic-samples)
                             coverage
                             #:check-lean? with-lean?
                             #:lean-fuel lean-fuel
                             #:lean-timeout lean-timeout
                             #:lean-batch-size lean-batch-size
                             #:redex-step-limit redex-step-limit
                             #:redex-timeout redex-timeout
                             #:racket-timeout racket-timeout)
  (for ([camp (in-list campaigns)])
    (when verbose?
      (printf "campaign ~a: ~a samples\n"
              (campaign-name camp)
              (campaign-count camp)))
    (for ([batch-start (in-range 0 (campaign-count camp) sample-batch-size)])
      (define batch-end
        (min (campaign-count camp)
             (+ batch-start sample-batch-size)))
      (compare-prepared-samples!
       (collect-campaign-sample-batch camp batch-start batch-end)
       coverage
       #:check-lean? with-lean?
       #:lean-fuel lean-fuel
       #:lean-timeout lean-timeout
       #:lean-batch-size lean-batch-size
       #:redex-step-limit redex-step-limit
       #:redex-timeout redex-timeout
       #:racket-timeout racket-timeout)))
  (define elapsed-ms (- (current-inexact-milliseconds) start))
  (when verbose?
    (printf "seed: ~a\n" seed)
    (printf "lean oracle: ~a\n"
            (if with-lean?
                (lean-runner-description)
                "disabled"))
    (printf "elapsed: ~a ms\n" (inexact->exact (round elapsed-ms)))
    (printf "coverage:\n")
    (for ([row (in-list (coverage-summary coverage))])
      (match-define (list name count) row)
      (printf "  ~a: ~a\n" name count)))
  coverage)

(define (run-random-suite! #:evaluation-campaigns [evaluation-campaigns default-main-campaigns]
                           #:soundness-campaigns [soundness-campaigns default-main-soundness-campaigns]
                           #:seed [seed 20260320]
                           #:soundness-seed [soundness-seed seed]
                           #:verbose? [verbose? #t]
                           #:with-lean? [with-lean? (lean-interpreter-available?)]
                           #:with-soundness? [with-soundness? #t]
                           #:lean-fuel [lean-fuel 2000]
                           #:lean-timeout [lean-timeout 5]
                           #:lean-batch-size [lean-batch-size 50]
                           #:sample-batch-size [sample-batch-size 200]
                           #:redex-step-limit [redex-step-limit 1000]
                           #:redex-timeout [redex-timeout 0.5]
                           #:racket-timeout [racket-timeout 0.5])
  (when verbose?
    (printf "evaluation checks:\n"))
  (define eval-coverage
    (run-random-checks! #:campaigns evaluation-campaigns
                        #:seed seed
                        #:verbose? verbose?
                        #:with-lean? with-lean?
                        #:lean-fuel lean-fuel
                        #:lean-timeout lean-timeout
                        #:lean-batch-size lean-batch-size
                        #:sample-batch-size sample-batch-size
                        #:redex-step-limit redex-step-limit
                        #:redex-timeout redex-timeout
                        #:racket-timeout racket-timeout))
  (define soundness-coverage
    (and with-soundness?
         (begin
           (when verbose?
             (printf "soundness checks:\n"))
           (run-soundness-checks! #:campaigns soundness-campaigns
                                  #:seed soundness-seed
                                  #:verbose? verbose?))))
  (hasheq 'evaluation eval-coverage
          'soundness soundness-coverage))

(module+ test
  (define suite
    (run-random-suite! #:evaluation-campaigns default-test-campaigns
                       #:soundness-campaigns default-test-soundness-campaigns
                       #:seed 20260320
                       #:verbose? #f))
  (define coverage
    (hash-ref suite 'evaluation))
  (define soundness-coverage
    (hash-ref suite 'soundness))
  (for ([name (in-list '(monitor prompt-tag/c mark/c list/c -> % abort call/comp call/cm ccm make-prompt-tag make-cm-key))])
    (check-true
     (positive? (hash-ref coverage name 0))
     (format "expected coverage for ~a" name)))
  (for ([name (in-list '(if λ case cons % abort call/comp call/cm ccm wcm make-prompt-tag make-cm-key))])
    (check-true
     (positive? (hash-ref soundness-coverage name 0))
     (format "expected soundness coverage for ~a" name))))

(module+ main
  (run-random-suite!))
