#lang racket

;; Dimoulas 2012 — randomized theorem-shape testing.
;;
;; Rediscovers known-false theorem shapes (e.g., single-step
;; preservation_loose is wrong — the correct form is multi-step
;; convergence) and validates candidate statements before proof work.
;;
;; Lean counterparts:
;;   - ContractModels.Dimoulas2012.Preservation.preservation{,_intermediate,_multi}
;;   - ContractModels.Dimoulas2012.Progress.progress_intermediate
;;   - ContractModels.Dimoulas2012.CompleteMonitoring.completeMonitoring
;;   - ContractModels.Dimoulas2012.NotComplete.{lax,picky}_not_complete

(require racket/list
         racket/match
         racket/pretty
         rackunit
         redex/reduction-semantics
         "model.rkt"
         "random.rkt")

(provide run-cm2012-theorem-checks!)

(define typed-label "τ")

(define (term->string t)
  (with-output-to-string
    (λ ()
      (pretty-write t))))

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

(define (lean-answer->answer j)
  (match j
    [`("int" ,n) `(int ,n)]
    [`("bool" ,b) `(bool ,b)]
    [`("unit") '(unit)]
    [`("procedure") '(procedure)]
    [`("ctc-error" ,k ,j0) `(ctc-error ,k ,j0)]
    [`("timeout") '(timeout)]
    [`("stuck") '(stuck)]
    [else
     (error 'lean-answer->answer "unexpected Lean answer ~s" j)]))

(define (lean-jsexpr->ty j)
  (match j
    ['null #f]
    [`("Num") 'Num]
    [`("Bool") 'Bool]
    [`("Unit") 'Unit]
    [`("->" ,t1 ,t2) `(→ ,(lean-jsexpr->ty t1) ,(lean-jsexpr->ty t2))]
    [`("Con" ,t) `(Con ,(lean-jsexpr->ty t))]
    [else (error 'lean-jsexpr->ty "unexpected Lean type ~s" j)]))

(define (cm2012-types e)
  (judgment-holds (cm2012-tc · ,e t) t))

(define (redex-value? e)
  (redex-match? cm2012-lang v e))

(define (redex-nexts e)
  (apply-reduction-relation cm2012-red e))

(define (canonical-binder n)
  (string->symbol (format "_b~a" n)))

(define (alpha-normalize-contract c env next)
  (match c
    [`(flat ,e1)
     (define-values (e1* next*) (alpha-normalize-expr e1 env next))
     (values `(flat ,e1*) next*)]
    [`(flatAnnot ,e1 ,ls)
     (define-values (e1* next*) (alpha-normalize-expr e1 env next))
     (values `(flatAnnot ,e1* ,ls) next*)]
    [`(-> ,c1 ,c2)
     (define-values (c1* next1) (alpha-normalize-contract c1 env next))
     (define-values (c2* next2) (alpha-normalize-contract c2 env next1))
     (values `(-> ,c1* ,c2*) next2)]
    [else
     (values c next)]))

(define (alpha-normalize-expr e env next)
  (match e
    [(? symbol?) (values (hash-ref env e e) next)]
    [(or (? integer?) (? boolean?) 'unit) (values e next)]
    [`(λ (,x : ,t) ,body)
     (define x* (canonical-binder next))
     (define-values (body* next*) (alpha-normalize-expr body (hash-set env x x*) (add1 next)))
     (values `(λ (,x* : ,t) ,body*) next*)]
    [`(μ (,x : ,t) ,body)
     (define x* (canonical-binder next))
     (define-values (body* next*) (alpha-normalize-expr body (hash-set env x x*) (add1 next)))
     (values `(μ (,x* : ,t) ,body*) next*)]
    [`(if ,e1 ,e2 ,e3)
     (define-values (e1* next1) (alpha-normalize-expr e1 env next))
     (define-values (e2* next2) (alpha-normalize-expr e2 env next1))
     (define-values (e3* next3) (alpha-normalize-expr e3 env next2))
     (values `(if ,e1* ,e2* ,e3*) next3)]
    [`(,op ,e1)
     #:when (memq op '(- not zero? number? boolean? unit?))
     (define-values (e1* next*) (alpha-normalize-expr e1 env next))
     (values `(,op ,e1*) next*)]
    [`(monitor ,ctc ,e1 ,k ,l ,j)
     (define-values (ctc* next1) (alpha-normalize-contract ctc env next))
     (define-values (e1* next2) (alpha-normalize-expr e1 env next1))
     (values `(monitor ,ctc* ,e1* ,k ,l ,j) next2)]
    [`(check ,e1 ,v ,k ,j)
     (define-values (e1* next1) (alpha-normalize-expr e1 env next))
     (define-values (v* next2) (alpha-normalize-expr v env next1))
     (values `(check ,e1* ,v* ,k ,j) next2)]
    [`(ctc-error ,_ ,_) (values e next)]
    [`(own ,e1 ,l)
     (define-values (e1* next*) (alpha-normalize-expr e1 env next))
     (values `(own ,e1* ,l) next*)]
    [`(,e1 ,e2)
     (define-values (e1* next1) (alpha-normalize-expr e1 env next))
     (define-values (e2* next2) (alpha-normalize-expr e2 env next1))
     (values `(,e1* ,e2*) next2)]
    [else
     (values e next)]))

(define (alpha-normalize e)
  (define-values (e* _next) (alpha-normalize-expr e (hash) 0))
  e*)

(define (expr-equiv? e1 e2)
  (equal? (alpha-normalize e1) (alpha-normalize e2)))

(define (reachable-within roots fuel)
  (let loop ([frontier (remove-duplicates roots equal?)]
             [seen (remove-duplicates roots equal?)]
             [remaining fuel])
    (cond
      [(zero? remaining) seen]
      [(null? frontier) seen]
      [else
       (define next-frontier
         (remove-duplicates
          (append-map redex-nexts frontier)
          equal?))
       (define fresh
         (filter (λ (e) (not (member e seen equal?))) next-frontier))
       (loop fresh
             (append seen fresh)
             (sub1 remaining))])))

(define (shares-common-reduct-within? e1 e2 fuel)
  (define reach1 (reachable-within (list e1) fuel))
  (define reach2 (reachable-within (list e2) fuel))
  (ormap (λ (candidate1)
           (ormap (λ (candidate2) (expr-equiv? candidate1 candidate2))
                  reach2))
         reach1))

(define (number-flat-contract)
  '(flat (λ (x : Num) (number? x))))

(define (bool-flat-contract)
  '(flat (λ (x : Bool) (boolean? x))))

(define (num->num-contract)
  `(-> ,(number-flat-contract) ,(number-flat-contract)))

(define bad-preservation-loose-input
  '(own (μ (x : Num) 0) "μ"))

(define bad-preservation-loose-output
  '(own 0 "μ"))

(define (interesting-candidate-exprs)
  (remove-duplicates
   (append
    (list
     0
     1
     #t
     #f
     'unit
     'f
     '(λ (x : Num) x)
     '(λ (x : Bool) x)
     '(μ (x : Num) x)
	     '(ctc-error "k" "j")
	     '((ctc-error "k" "j") unit)
	     '(((ctc-error "k" "j") unit) unit)
	     '(f (μ (x : Num) x))
	     bad-preservation-loose-input
	     bad-preservation-loose-output
	     '(if #t 0 1)
	     '(if #f 0 1)
     '(if (ctc-error "k" "j") 0 1)
     '(check #t 0 "τ" "j")
     '(check #f 0 "τ" "j")
     '(monitor (flat (λ (x : Num) (number? x))) 0 "τ" "υ" "j")
     '(monitor (flat (λ (x : Num) (number? x))) (own 0 "τ") "τ" "υ" "j")
     '(monitor (-> (flat (λ (x : Num) (number? x)))
                   (flat (λ (x : Num) (number? x))))
               (λ (x : Num) x)
               "τ" "υ" "j")
     '(own (own (λ (x : Num) x) "τ") "τ")
     '(own (μ (x : Num) x) "τ")
     '(not #t)
     '(- 0)
     '(zero? 0)
     '(number? unit)
     '(boolean? 0)
     '(unit? unit))
    (for/list ([base (in-list '(0 #t #f unit f (ctc-error "k" "j")))])
      `(own ,base "τ"))
    (for/list ([base (in-list '(0 #t #f unit f (ctc-error "k" "j")))])
      `(if ,base 0 1))
    (for/list ([base (in-list '(0 #t #f unit f (ctc-error "k" "j")))])
      `(check ,base 0 "τ" "j"))
    (for*/list ([fun (in-list '((λ (x : Num) x)
                                (own (λ (x : Num) x) "τ")
                                f
                                (ctc-error "k" "j")))]
                [arg (in-list '(0 #t unit (μ (x : Num) x) (own 0 "τ")))])
      `(,fun ,arg))
    (for/list ([v (in-list '(0 #t unit (λ (x : Num) x) (own 0 "τ")))])
      `(monitor ,(number-flat-contract) ,v "τ" "υ" "j"))
    (for/list ([v (in-list '((λ (x : Num) x)
                             (own (λ (x : Num) x) "τ")))])
      `(monitor ,(num->num-contract) ,v "τ" "υ" "j")))
   equal?))

(define (lean-step-expr result)
  (lean-jsexpr->expr (hash-ref result 'stepResult)))

(define (lean-final-expr result)
  (lean-jsexpr->expr (hash-ref result 'finalExpr)))

(define (query-results exprs)
  (lean-run-batches
   (for/list ([expr (in-list exprs)])
     (query->lean-jsexpr expr typed-label))))

(define (find-step-sound-exact-counterexample exprs results)
  (for/first ([pair (in-list (map list exprs results))]
              #:do [(define expr (first pair))
                    (define result (second pair))
                    (define lean-step (lean-step-expr result))
                    (define nexts (redex-nexts expr))]
              #:when (and lean-step
                          (not (member lean-step nexts equal?))))
    (hasheq 'expr expr
            'lean-step lean-step
            'redex-nexts nexts)))

(define (find-infer-type-counterexample exprs results)
  (for/first ([pair (in-list (map list exprs results))]
              #:do [(define expr (first pair))
                    (define result (second pair))
                    (define redex-types (remove-duplicates (cm2012-types expr) equal?))
                    (define lean-type (lean-jsexpr->ty (hash-ref result 'initialType)))]
              #:when
              (cond
                [(null? redex-types) lean-type]
                [(= (length redex-types) 1)
                 (not (equal? (car redex-types) lean-type))]
                [else #t]))
    (hasheq 'expr expr
            'redex-types redex-types
            'lean-type lean-type)))

(define (find-step-complete-exact-counterexample exprs results)
  (for*/first ([pair (in-list (map list exprs results))]
               #:do [(define expr (first pair))
                     (define result (second pair))
                     (define lean-step (lean-step-expr result))]
               [next (in-list (redex-nexts expr))]
               #:when (not (equal? lean-step next)))
    (hasheq 'expr expr
            'lean-step lean-step
            'redex-next next)))

(define (find-step-complete-exists-counterexample exprs results)
  (for/first ([pair (in-list (map list exprs results))]
              #:do [(define expr (first pair))
                    (define result (second pair))
                    (define nexts (redex-nexts expr))]
              #:when (and (pair? nexts)
                          (not (lean-step-expr result))))
    (hasheq 'expr expr
            'redex-nexts nexts)))

(define (find-preservation-loose-counterexample exprs results)
  (define input-result
    (for/first ([pair (in-list (map list exprs results))]
                #:when (equal? (first pair) bad-preservation-loose-input))
      (second pair)))
  (define output-result
    (for/first ([pair (in-list (map list exprs results))]
                #:when (equal? (first pair) bad-preservation-loose-output))
      (second pair)))
  (and input-result
       output-result
       (hash-ref input-result 'initialRepairWF)
       (member bad-preservation-loose-output (redex-nexts bad-preservation-loose-input) equal?)
       (not (hash-ref output-result 'initialIntermWF))
       (hasheq 'expr bad-preservation-loose-input
               'redex-next bad-preservation-loose-output
               'lean-initial-repair (hash-ref input-result 'initialRepairWF)
               'lean-initial-interm-after-step
               (hash-ref output-result 'initialIntermWF))))

(define (find-step-simulation-counterexample exprs results #:fuel [fuel 6])
  (for/first ([pair (in-list (map list exprs results))]
              #:do [(define expr (first pair))
                    (define result (second pair))
                    (define lean-step (lean-step-expr result))
                    (define nexts (redex-nexts expr))]
              #:when (and lean-step
                          (not (ormap (λ (next)
                                        (shares-common-reduct-within? lean-step next fuel))
                                      nexts))))
    (hasheq 'expr expr
            'lean-step lean-step
            'redex-nexts nexts)))

(define (find-eval-trace-simulation-counterexample exprs results #:fuel [fuel 12])
  (for/first ([pair (in-list (map list exprs results))]
              #:do [(define expr (first pair))
                    (define result (second pair))
                    (define lean-final (lean-final-expr result))
                    (define timed-out? (hash-ref result 'timedOut))
                    (define steps (hash-ref result 'steps))]
              #:when (and (not timed-out?)
                          (<= steps fuel)
                          (not (shares-common-reduct-within? expr lean-final fuel))))
    (hasheq 'expr expr
            'lean-final lean-final)))

(define (source-samples samples expr-fuel)
  (for/list ([i (in-range samples)])
    (define label (random-label))
    (define type (random-type))
    (list label type (gen-expr expr-fuel '() label type))))

(define (check-source-sample! label type expr result)
  (define redex-types (cm2012-types expr))
  (unless (member type redex-types equal?)
    (error 'check-source-sample!
           "Redex rejected theorem-test source sample\nexpected: ~s\nredex types: ~s\nterm:\n~a"
           type redex-types (term->string expr)))
  (unless (hash-ref result 'wfSource)
    (error 'check-source-sample!
           "Lean wfSource rejected theorem-test source sample\nterm:\n~a"
           (term->string expr)))
  (unless (or (redex-value? expr)
              (pair? (redex-nexts expr)))
    (error 'check-source-sample!
           "Redex found a source-progress counterexample\nterm:\n~a"
           (term->string expr)))
  (define redex-answer (normalize-answer (cm2012-eval/answer expr #:fuel 200)))
  (define lean-answer (lean-answer->answer (hash-ref result 'answer)))
  (unless (equal? redex-answer lean-answer)
    (error 'check-source-sample!
           "Redex/Lean source answer mismatch\nredex: ~s\nlean: ~s\nterm:\n~a"
            redex-answer lean-answer (term->string expr)))
  (unless (hash-ref result 'preservesType)
    (error 'check-source-sample!
           "Lean preservation approximation failed on theorem-test source sample\nterm:\n~a"
           (term->string expr)))
  (hasheq 'traceLayeredWF (hash-ref result 'traceLayeredWF)
          'traceRepairSettlement
          (or (hash-ref result 'timedOut)
              (hash-ref result 'traceRepairSettlement))
          'completeMonitoring (hash-ref result 'completeMonitoring)))

(define (summarize-counterexample name ce)
  (string-append
   (format "~a counterexample\n" name)
   (string-join
    (for/list ([kv (in-list (sort (hash->list ce) symbol<? #:key car))])
      (format "  ~a: ~a" (car kv) (term->string (cdr kv))))
    "\n")))

(define (run-cm2012-theorem-checks! #:seed [seed 20260323]
                                    #:candidate-samples [candidate-samples 24]
                                    #:source-samples [source-count 24]
                                    #:expr-fuel [expr-fuel 3]
                                    #:simulation-fuel [simulation-fuel 6]
                                    #:verbose? [verbose? #t])
  (random-seed seed)
  (define base-candidates (interesting-candidate-exprs))
  (define extra-candidates
    (for/list ([i (in-range candidate-samples)])
      (define label (random-label))
      (define type (random-type))
      (gen-expr expr-fuel '() label type)))
  (define candidates
    (remove-duplicates (append base-candidates extra-candidates) equal?))
  (define candidate-results (query-results candidates))
  (define ce-sound-exact
    (find-step-sound-exact-counterexample candidates candidate-results))
  (define ce-infer-type
    (find-infer-type-counterexample candidates candidate-results))
  (define ce-complete-exact
    (find-step-complete-exact-counterexample candidates candidate-results))
  (define ce-complete-exists
    (find-step-complete-exists-counterexample candidates candidate-results))
  (define ce-preservation-loose
    (find-preservation-loose-counterexample candidates candidate-results))
  (unless ce-sound-exact
    (error 'run-cm2012-theorem-checks!
           "failed to refute the known-false exact step soundness statement"))
  (when ce-infer-type
    (error 'run-cm2012-theorem-checks!
           "bounded search found a counterexample to CM2012 infer-type correspondence\n~a"
           (summarize-counterexample 'infer-type ce-infer-type)))
  (unless ce-complete-exact
    (error 'run-cm2012-theorem-checks!
           "failed to refute the known-false exact step completeness statement"))
  (unless ce-complete-exists
    (error 'run-cm2012-theorem-checks!
           "failed to refute the known-false existential step completeness statement"))
  (unless ce-preservation-loose
    (error 'run-cm2012-theorem-checks!
           "failed to refute the known-false repair single-step preservation statement"))
  (define ce-step-sim
    (find-step-simulation-counterexample
     candidates candidate-results
     #:fuel simulation-fuel))
  (when ce-step-sim
    (error 'run-cm2012-theorem-checks!
           "bounded search found a counterexample to the corrected step simulation statement\n~a"
           (summarize-counterexample 'step-simulation ce-step-sim)))
  (define ce-eval-sim
    (find-eval-trace-simulation-counterexample
     candidates candidate-results
     #:fuel (* 2 simulation-fuel)))
  (when ce-eval-sim
    (error 'run-cm2012-theorem-checks!
           "bounded search found a counterexample to the eval-trace simulation statement\n~a"
           (summarize-counterexample 'eval-trace-simulation ce-eval-sim)))
  (define source-samples*
    (source-samples source-count expr-fuel))
  (define source-results
    (lean-run-batches
     (for/list ([sample (in-list source-samples*)])
       (match-define (list label _type expr) sample)
       (query->lean-jsexpr expr label))))
  (define trace-layered-misses 0)
  (define trace-repair-settlement-misses 0)
  (define complete-monitoring-misses 0)
  (for ([sample (in-list source-samples*)]
        [result (in-list source-results)])
    (match-define (list label type expr) sample)
    (define summary (check-source-sample! label type expr result))
    (unless (hash-ref summary 'traceLayeredWF)
      (set! trace-layered-misses (add1 trace-layered-misses)))
    (unless (hash-ref summary 'traceRepairSettlement)
      (set! trace-repair-settlement-misses (add1 trace-repair-settlement-misses)))
    (unless (hash-ref summary 'completeMonitoring)
      (set! complete-monitoring-misses (add1 complete-monitoring-misses))))
  (when verbose?
    (printf "cm2012 theorem checks passed\n")
    (printf "seed: ~a\n" seed)
    (printf "candidate terms: ~a\n" (length candidates))
    (printf "source samples: ~a\n" source-count)
    (printf "simulation fuel: ~a\n" simulation-fuel)
    (printf "trace-layered misses: ~a\n" trace-layered-misses)
    (printf "trace-repair-settlement misses: ~a\n" trace-repair-settlement-misses)
    (printf "complete-monitoring approx misses: ~a\n" complete-monitoring-misses)
    (printf "known false theorems rediscovered:\n")
    (printf "  step soundness exact target\n")
    (printf "  step completeness exact target\n")
    (printf "  step completeness existential target\n")
    (printf "  repair single-step preservation (preservation_loose)\n")
    (printf "bounded-valid theorem shapes:\n")
    (printf "  infer-type correspondence\n")
    (printf "  step simulation\n")
    (printf "  short-trace eval-trace simulation\n")
    (printf "  source progress / preservation\n")
    (printf "soft signal only:\n")
    (printf "  reachable layered subject / repair settlement\n")
    (printf "  complete-monitoring approximation\n")))

(module+ test
  (run-cm2012-theorem-checks! #:candidate-samples 12
                              #:source-samples 12
                              #:expr-fuel 2
                              #:simulation-fuel 4
                              #:verbose? #f))

(module+ main
  (run-cm2012-theorem-checks!))
