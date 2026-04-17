#lang racket

;; Dimoulas 2012 — randomized blame-correctness testing.
;;
;; Exercises the well-formedness judgments defined in blame.rkt
;; (wfp, wfctc, wfip, lwfp, ctcwitnessp) on generated programs to catch
;; issues in the blame-witness / complete-monitoring statements.
;;
;; Lean counterpart:
;;   - ContractModels.Dimoulas2012.Witness.ctcError_has_witness
;;   - ContractModels.Dimoulas2012.CompleteMonitoring.completeMonitoring

(require racket/list
         racket/match
         rackunit
         redex/reduction-semantics
         (except-in "../takikawa2013/model.rkt" let)
         "blame.rkt")

(provide run-blame-random-checks!)

(define typed-label "τ")
(define untyped-label "υ")
(define contract-label "j")

(define available-label-sets
  (list (list typed-label)
        (list untyped-label)
        (list typed-label untyped-label)))

(define base-types
  '(Num Bool Unit))

(define fixed-owner-env
  `(tag0 : ,typed-label
         (tag1 : ,untyped-label
               (key0 : ,typed-label
                     (key1 : ,untyped-label ·)))))

(define fixed-store
  '(tag0 (tag1 (key0 (key1 ·)))))

(define (random-label)
  (if (zero? (random 2))
      typed-label
      untyped-label))

(define (other-label l)
  (if (equal? l typed-label)
      untyped-label
      typed-label))

(define (tag-for-label l)
  (if (equal? l typed-label) 'tag0 'tag1))

(define (key-for-label l)
  (if (equal? l typed-label) 'key0 'key1))

(define (random-base-type)
  (list-ref base-types (random (length base-types))))

(define (flat-predicate-body t x)
  (match t
    ['Num `(number? ,x)]
    ['Bool `(boolean? ,x)]
    ['Unit `(unit? ,x)]
    [else `(number? ,x)]))

(define (gen-value-for-type t owner)
  (match t
    ['Num (random 7)]
    ['Bool (zero? (random 2))]
    ['Unit 'unit]
    [`(List ,elem)
     (if (zero? (random 2))
         `(null ,elem)
         `(cons ,(gen-value-for-type elem owner)
                (null ,elem)))]
    [`(→ ,dom ,cod)
     (define x (gensym 'x))
     `(λ (,x : ,dom) ,(gen-value-for-type cod owner))]
    [`(Prompt ,_ ,_)
     (tag-for-label owner)]
    [`(Mark ,_)
     (key-for-label owner)]
    [else 0]))

(define (strip-own e)
  (match e
    [`(own ,inner ,_) (strip-own inner)]
    [`(λ (,x : ,t) ,body)
     `(λ (,x : ,t) ,(strip-own body))]
    [`(,op ,e1 ,e2)
     `(,op ,(strip-own e1) ,(strip-own e2))]
    [`(,op ,e1)
     `(,op ,(strip-own e1))]
    [`(if ,e1 ,e2 ,e3)
     `(if ,(strip-own e1) ,(strip-own e2) ,(strip-own e3))]
    [`(cons ,e1 ,e2)
     `(cons ,(strip-own e1) ,(strip-own e2))]
    [`(case ,e1 (null = ,e2) ((cons ,x1 ,x2) = ,e3))
     `(case ,(strip-own e1)
        (null = ,(strip-own e2))
        ((cons ,x1 ,x2) = ,(strip-own e3)))]
    [else e]))

(define (erase-oblig ctc)
  (match ctc
    [`(oblig (flat ,e) ,_)
     `(flat ,(strip-own e))]
    [`(-> ,c1 ,c2)
     `(-> ,(erase-oblig c1) ,(erase-oblig c2))]
    [`(prompt-tag/c ,c1 ,c2 ,t1 ,t2)
     `(prompt-tag/c ,(erase-oblig c1) ,(erase-oblig c2) ,t1 ,t2)]
    [`(mark/c ,c ,t)
     `(mark/c ,(erase-oblig c) ,t)]
    [`(list/c ,c)
     `(list/c ,(erase-oblig c))]
    [else ctc]))

(define (gen-wf-contract depth pos-labels neg-labels)
  (if (zero? depth)
      (let* ([t (random-base-type)]
             [x (gensym 'x)])
        (values
         `(oblig (flat (own (λ (,x : ,t) ,(flat-predicate-body t x))
                            ,contract-label))
                 ,pos-labels)
         t))
      (case (random 5)
        [(0)
         (define-values (inner t)
           (gen-wf-contract 0 pos-labels neg-labels))
         (values inner t)]
        [(1)
         (define-values (dom t-dom)
           (gen-wf-contract (sub1 depth) neg-labels pos-labels))
         (define-values (cod t-cod)
           (gen-wf-contract (sub1 depth) pos-labels neg-labels))
         (values `(-> ,dom ,cod) `(→ ,t-dom ,t-cod))]
        [(2)
         (define-values (abort-ctc t-abort)
           (gen-wf-contract (sub1 depth) pos-labels neg-labels))
         (define-values (comp-ctc t-comp)
           (gen-wf-contract (sub1 depth) pos-labels neg-labels))
         (values `(prompt-tag/c ,abort-ctc ,comp-ctc ,t-abort ,t-comp)
                 `(Prompt ,t-abort ,t-comp))]
        [(3)
         (define-values (inner t)
           (gen-wf-contract (sub1 depth) pos-labels neg-labels))
         (values `(mark/c ,inner ,t) `(Mark ,t))]
        [else
         (define-values (inner t)
           (gen-wf-contract (sub1 depth) pos-labels neg-labels))
         (values `(list/c ,inner) `(List ,t))])))

(define (gen-source depth l)
  (if (zero? depth)
      (case (random 7)
        [(0) (random 7)]
        [(1) (zero? (random 2))]
        [(2) 'unit]
        [(3) `(null ,(random-base-type))]
        [(4) (tag-for-label l)]
        [(5) (key-for-label l)]
        [else `(own ,(random 7) ,l)])
      (case (random 10)
        [(0) `(if #t ,(gen-source (sub1 depth) l) ,(gen-source (sub1 depth) l))]
        [(1) `(cons ,(gen-source (sub1 depth) l) ,(gen-source (sub1 depth) l))]
        [(2) (define x (gensym 'x))
             `(λ (,x : Num) ,(gen-source (sub1 depth) l))]
        [(3) `((λ (x : Num) ,(gen-source (sub1 depth) l)) ,(gen-source 0 l))]
        [(4) `(wcm ((,(key-for-label l) ,(gen-value-for-type 'Num l)))
                    ,(gen-source (sub1 depth) l))]
        [(5) `(ccm ,(key-for-label l) Num)]
        [(6) `(% ,(gen-source (sub1 depth) l)
                 ,(tag-for-label l)
                 (λ (x : Num) ,(gen-source (sub1 depth) l)))]
        [(7) `(call/comp (λ (k : (→ Num Num)) ,(gen-source 0 l))
                         ,(tag-for-label l))]
        [(8) `(call/cm ,(key-for-label l)
                       ,(gen-value-for-type 'Num l)
                       ,(gen-source (sub1 depth) l))]
        [else
         (define k (other-label l))
         (define-values (ctc t)
           (gen-wf-contract 2 (list k) (list l)))
         `(monitor ,ctc
                   (own ,(gen-value-for-type t k) ,k)
                   ,k ,l ,contract-label)])))

(define (gen-loose-term depth l)
  (case (random 2)
    [(0)
     `((own ,(gen-source depth l) ,l) ,(gen-source depth l))]
    [else
     `(ccm (own ,(gen-source depth l) ,l) Num)]))

(define (top-contract-tag ctc)
  (match ctc
    [`(oblig . ,_) 'flat]
    [`(-> . ,_) '->]
    [`(prompt-tag/c . ,_) 'prompt-tag/c]
    [`(mark/c . ,_) 'mark/c]
    [`(list/c . ,_) 'list/c]
    [_ 'other]))

(define (top-expr-tag e)
  (match e
    [`(if . ,_) 'if]
    [`(cons . ,_) 'cons]
    [`(λ . ,_) 'λ]
    [`(% . ,_) '%]
    [`(call/comp . ,_) 'call/comp]
    [`(call/cm . ,_) 'call/cm]
    [`(wcm . ,_) 'wcm]
    [`(ccm . ,_) 'ccm]
    [`(monitor . ,_) 'monitor]
    [`(own . ,_) 'own]
    [(? number?) 'Num]
    [(? boolean?) 'Bool]
    ['unit 'Unit]
    [`(null . ,_) 'null]
    [(? symbol?) 'symbol]
    [_ 'other]))

(define (increment-counts counts key)
  (hash-update counts key add1 0))

(define (run-blame-random-checks! #:contract-count [contract-count 1000]
                                  #:source-count [source-count 1000]
                                  #:loose-count [loose-count 500]
                                  #:seed [seed 20260321]
                                  #:verbose? [verbose? #t])
  (random-seed seed)
  (unless (judgment-holds (lwfp · (x : "τ" ·) "τ" x))
    (error 'run-blame-random-checks!
           "lwfp should accept same-owner loose variables"))
  (when (judgment-holds (lwfp · (x : "τ" ·) "υ" x))
    (error 'run-blame-random-checks!
           "lwfp should reject cross-owner loose variables"))
  (define contract-counts (make-hash))
  (define source-counts (make-hash))

  (for ([i (in-range contract-count)])
    (define pos-labels (list-ref available-label-sets (random (length available-label-sets))))
    (define neg-labels (list-ref available-label-sets (random (length available-label-sets))))
    (define-values (ctc ty)
      (gen-wf-contract 3 pos-labels neg-labels))
    (hash-set! contract-counts (top-contract-tag ctc)
               (add1 (hash-ref contract-counts (top-contract-tag ctc) 0)))
    (unless (judgment-holds (wfctc ,fixed-owner-env · ,pos-labels ,neg-labels ,contract-label ,ctc))
      (error 'run-blame-random-checks!
             "wfctc rejected generated contract\nlabels+: ~s\nlabels-: ~s\ncontract:\n~s"
             pos-labels neg-labels ctc))
    (unless (judgment-holds (wfctci ,fixed-owner-env · ,pos-labels ,neg-labels ,contract-label ,ctc))
      (error 'run-blame-random-checks!
             "wfctci rejected generated contract\nlabels+: ~s\nlabels-: ~s\ncontract:\n~s"
             pos-labels neg-labels ctc))
    (unless (equal? (term (ctc->type ,ctc)) ty)
      (error 'run-blame-random-checks!
             "ctc->type mismatch\ncontract:\n~s\nexpected: ~s\ngot: ~s"
             ctc ty (term (ctc->type ,ctc))))
    (unless (member ty (judgment-holds (tc · · ,(erase-oblig ctc) (Con t)) t) equal?)
      (error 'run-blame-random-checks!
             "model tc rejected erased obligation contract\ncontract:\n~s\nerased:\n~s\nexpected: ~s"
             ctc (erase-oblig ctc) ty)))

  (unless (judgment-holds (wfst ,fixed-owner-env ,fixed-store))
    (error 'run-blame-random-checks!
           "fixed proof-layer store is not well formed"))
  (unless (judgment-holds (wfip ,fixed-owner-env · "τ" (ctc-error "τ" "j")))
    (error 'run-blame-random-checks!
           "wfip should accept contract errors as intermediate states"))
  (when (judgment-holds
         (wfip ,fixed-owner-env · "τ"
               (check #t ((λ (x : Num) x) 0) "τ" "j")))
    (error 'run-blame-random-checks!
           "wfip should reject check states whose witness side is not a value"))

  (for ([i (in-range source-count)])
    (define l (random-label))
    (define e (gen-source 3 l))
    (hash-set! source-counts (top-expr-tag e)
               (add1 (hash-ref source-counts (top-expr-tag e) 0)))
    (unless (judgment-holds (wfsp ,fixed-owner-env · ,l ,e))
      (error 'run-blame-random-checks!
             "wfsp rejected generated source term\nlabel: ~s\nterm:\n~s"
             l e))
    (unless (judgment-holds (wfip ,fixed-owner-env · ,l ,e))
      (error 'run-blame-random-checks!
             "wfip rejected generated source term\nlabel: ~s\nterm:\n~s"
             l e)))

  (for ([i (in-range loose-count)])
    (define l (random-label))
    (define e (gen-loose-term 2 l))
    (unless (judgment-holds (lwfp ,fixed-owner-env · ,l ,e))
      (error 'run-blame-random-checks!
             "lwfp rejected generated loose term\nlabel: ~s\nterm:\n~s"
             l e))
    (unless (judgment-holds (wfip ,fixed-owner-env · ,l ,e))
      (error 'run-blame-random-checks!
             "wfip rejected generated loose term\nlabel: ~s\nterm:\n~s"
             l e)))

  (unless (judgment-holds
           (ctcwitnessp
            (monitor (oblig (flat (own (λ (x : Num) (zero? x)) ,contract-label))
                            (,typed-label))
                     (own 0 ,typed-label)
                     ,typed-label ,untyped-label ,contract-label)
            ,typed-label ,contract-label))
    (error 'run-blame-random-checks!
           "ctcwitnessp rejected canonical flat-monitor witness"))

  (when verbose?
    (printf "blame-layer contracts: ~a samples\n" contract-count)
    (printf "blame-layer sources: ~a samples\n" source-count)
    (printf "blame-layer loose terms: ~a samples\n" loose-count)
    (printf "contract coverage: ~s\n"
            (sort (hash->list contract-counts) symbol<? #:key car))
    (printf "source coverage: ~s\n"
            (sort (hash->list source-counts) symbol<? #:key car))))

(module+ test
  (run-blame-random-checks! #:contract-count 50
                            #:source-count 50
                            #:loose-count 25
                            #:verbose? #f))

(module+ main
  (run-blame-random-checks!))
