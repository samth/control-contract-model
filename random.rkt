#lang racket

(require rackunit
         redex/pict
         redex/reduction-semantics
         "model.rkt")

;; for racket-eval
(define-namespace-anchor anchor)

;; evaluator for racket
;; #:post is an optional procedure for doing post-processing on the
;; translated term (such as adding a predicate to evaluate)
(define (racket-eval t #:post [post-process values])
  (with-handlers ([exn:fail:contract:blame? (λ (e) (extract-blame e))]
                  [exn:fail? (λ (e) 'error)])
    (parameterize ([current-namespace (namespace-anchor->namespace anchor)])
      (eval (post-process (redex->racket t))))))

;; the actual evaluator
(define (racket-eval/answer t)
  (define result (racket-eval t))
  (define contract?
    (racket-eval t #:post (λ (t) `(contract? ,t))))
  (cond [(number? result) result]
        [(boolean? result) result]
        [(string? result) result]
        [(continuation-prompt-tag? result) 'prompt-tag]
        [(procedure? result) 'procedure]
        [(eq? 'error result) 'error]
        [(and (list? result)
              (eq? (car result) 'ctc-error))
         result]
        ;; TODO: hacky
        ;;       we say any non-procedure (i.e., non-flat) contract
        ;;       is just 'contract.
        [contract? 'contract]
        [else (error "Unexpected result")]))

;; take blame string from the exception and put it in ctc-error
(define (extract-blame e)
  (define blame (exn:fail:contract:blame-object e))
  `(ctc-error ,(format "~a" (blame-positive blame))))

;; table for storing prompt tag -> Racket prompt tag associations
(define *prompt-tag-table* (make-hash))

;; transform a redex term to racket term
(define (redex->racket t)
  (match t
    [`(λ (,x) ,e)
     `(λ (,x) ,(redex->racket e))]
    [`(if ,e_1 ,e_2 ,e_3)
     `(if ,(redex->racket e_1)
          ,(redex->racket e_2)
          ,(redex->racket e_3))]
    [`(monitor ,ctc ,e ,blame_p ,blame_n)
     `(contract ,(redex->racket ctc)
                ,(redex->racket e)
                ,(redex->racket blame_p)
                ,(redex->racket blame_n))]
    [`(flat ,v)
     `(flat-contract ,(redex->racket v))]
    [`(-> ,ctc_1 ,ctc_2)
     `(-> ,(redex->racket ctc_1) ,(redex->racket ctc_2))]
    [`(prompt-tag/c ,ctc)
     `(prompt-tag/c ,(redex->racket ctc))]
    ['(make-prompt-tag)
     '(make-continuation-prompt-tag)]
    [`(prompt-tag ,key)
     (define tag (hash-ref *prompt-tag-table* key #f))
     (or tag
         ;; let* here to avoid let binding in Redex
         (let* ([new-tag (make-continuation-prompt-tag)])
           (hash-set! *prompt-tag-table* key new-tag)
           new-tag))]
    [`(impersonate-prompt-tag ,e_p ,e_1 ,e_2)
     `(impersonate-prompt-tag ,(redex->racket e_p)
                              ,(redex->racket e_1)
                              ,(redex->racket e_2))]
    [`(prompt-tag? ,e)
     `(continuation-prompt-tag? ,(redex->racket e))]
    [`(,(and op (or '+ '- '* 'and 'or)) ,e_1 ,e_2)
     `(,op ,(redex->racket e_1) ,(redex->racket e_2))]
    [`(,(and op (or '- 'zero? 'procedure? 'number?
                    'not 'string? 'boolean? 'prompt-tag?))
       ,e)
     `(,op ,(redex->racket e))]
    [`(% ,e_1 ,e_2 ,e_3)
     `(call-with-continuation-prompt
       (λ () ,(redex->racket e_1))
       ,(redex->racket e_2)
       ,(redex->racket e_3))]
    [`(abort ,e_1 ,e_2)
     `(abort-current-continuation
       ,(redex->racket e_1) ,(redex->racket e_2))]
    ;; turn ctc-error terms into an exception with blame
    [`(ctc-error ,blame)
     `(contract number? 'will-fail ,blame "unobservable")]
    [`(,e_1 ,e_2)
     `(,(redex->racket e_1) ,(redex->racket e_2))]
    [x x]))

;; close-term
;; if the term contains free variables, bind them
(define-metafunction abort-lang
  [(close-term e) (close-term-helper e (free-vars e))])

(define-metafunction abort-lang
  [(close-term-helper e ()) e]
  [(close-term-helper e (x x_1 ...))
   ((λ (x) (close-term-helper e (x_1 ...)))
    0)])

(define-metafunction abort-lang
  [(free-vars (e_1 e_2))
   (∪ (free-vars e_1) (free-vars e_2))]
  [(free-vars (binop e_1 e_2))
   (∪ (free-vars e_1) (free-vars e_2))]
  [(free-vars (unop e)) (free-vars e)]
  [(free-vars x) (x)]
  [(free-vars (λ (x ...) e))
   (/ (free-vars e) (x ...))]
  [(free-vars (if e_1 e_2 e_3))
   (∪ (free-vars e_1) (free-vars e_2) (free-vars e_3))]
  [(free-vars (monitor ctc e blame_1 blame_2))
   (∪ (free-vars ctc) (free-vars e))]
  [(free-vars (flat v))
   (free-vars v)]
  [(free-vars (-> ctc_1 ctc_2))
   (∪ (free-vars ctc_1) (free-vars ctc_2))]
  [(free-vars (prompt-tag/c ctc))
   (free-vars ctc)]
  [(free-vars (% e_1 e_2 v))
   (∪ (free-vars e_1) (free-vars e_2) (free-vars v))]
  [(free-vars (abort e_1 e_2))
   (∪ (free-vars e_1) (free-vars e_2))]
  [(free-vars (impersonate-prompt-tag v_1 v_2 v_3))
   (∪ (free-vars v_1) (free-vars v_2) (free-vars v_3))]
  [(free-vars e) ()])

(define-metafunction abort-lang
  ∪ : (x ...) ... -> (x ...)
  [(∪ (x_1 ...) (x_2 ...) (x_3 ...) ...)
   (∪ (x_1 ... x_2 ...) (x_3 ...) ...)]
  [(∪ (x_1 ...))
   (x_1 ...)]
  [(∪) ()])

(define-metafunction abort-lang
  / : (x ...) (x ...) -> (x ...)
  [(/ (x ...) ()) (x ...)]
  [(/ (x_1 ... x_2 x_3 ...) (x_2 x_4 ...))
   (/ (x_1 ... x_3 ...) (x_2 x_4 ...))
   (side-condition (not (memq (term x_2) (term (x_3 ...)))))]
  [(/ (x_1 ...) (x_2 x_3 ...))
   (/ (x_1 ...) (x_3 ...))])

;; test the racket evaluator for equivalence
(module+ test
  (require rackunit)
  (check-equal?
   (racket-eval (term (+ 1 2)))
   3)
  (check-equal?
   (racket-eval (term (monitor (flat (λ (x) (number? x)))
                               5
                               "pos" "neg")))
   5)
  (check-equal?
   (racket-eval (term (monitor (flat (λ (x) (number? x)))
                               #t
                               "pos" "neg")))
   '(ctc-error "pos"))
  (check-true
   (continuation-prompt-tag? (racket-eval (term (make-prompt-tag)))))
  (check-equal?
   (racket-eval
    (term (let pt (make-prompt-tag)
            (% (abort pt 5)
               pt
               (λ (x) (+ x 1))))))
   6)
  (check-equal?
   (racket-eval
    (term (let do-prompt
            (let pt (make-prompt-tag)
              (monitor (-> (-> (prompt-tag/c (-> (flat (λ (x) (number? x)))
                                                 (flat (λ (x) (number? x)))))
                               (flat (λ (x) (void? x))))
                           (flat (λ (x) (number? x))))
                       (λ (f) (% (f pt)
                                 pt
                                 (λ (f) (f 0))))
                       "A"
                       "B"))
            (let do-prompt-2
              (monitor (-> (-> (prompt-tag/c (-> (flat (λ (x) (string? x)))
                                                 (flat (λ (x) (number? x)))))
                               (flat (λ (x) (void? x))))
                           (flat (λ (x) (number? x))))
                       (λ (f) (do-prompt f))
                       "B"
                       "C")
              (do-prompt-2 (λ (pt) (abort pt (λ (v) (+ v 1)))))))))
   '(ctc-error "B")))

(module+ main
  (redex-check
   abort-lang
   e
   (equal? (racket-eval/answer (term ((λ (x) (% (abort x e) x (λ (x_f) x_f))) (make-prompt-tag))))
           (abort-eval         (term ((λ (x) (% (abort x e) x (λ (x_f) x_f))) (make-prompt-tag)))))
   #:attempts 10000
   #:prepare (λ (t) (term (close-term ,t)))
   #:print? #t))
