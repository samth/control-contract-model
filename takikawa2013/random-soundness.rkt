#lang racket

;; Takikawa 2013 — randomized soundness testing campaigns.
;;
;; Generates well-typed mixed programs and checks preservation-style
;; properties on bounded reductions.
;;
;; Lean counterpart: Takikawa2013.Theorems.{preservation, preservation_loose}.

(require json
         racket/list
         racket/match
         racket/pretty
         racket/runtime-path
         rackunit
         redex/reduction-semantics
         (except-in "model.rkt" let)
         "random-typing.rkt")

(provide default-main-soundness-campaigns
         default-test-soundness-campaigns
         run-soundness-checks!)

(define-runtime-path model-dir ".")
(define project-root
  (simplify-path (build-path model-dir 'up 'up)))
(define lean-soundness-path
  (simplify-path
   (build-path project-root "ContractModels" "Takikawa2013" "Main" "Soundness.lean")))
(define built-lean-soundness-path
  (simplify-path
   (build-path project-root ".lake" "build" "bin" "takikawa2013-soundness")))

(define default-lean-soundness-command
  (if (file-exists? built-lean-soundness-path)
      (list (path->string built-lean-soundness-path))
      (list (or (find-executable-path "lake") "lake")
            "env"
            "lean"
            "--run"
            (path->string lean-soundness-path))))

(define (lean-soundness-command)
  (if (getenv "TSTH_LEAN_SOUNDNESS")
      (list (getenv "TSTH_LEAN_SOUNDNESS"))
      default-lean-soundness-command))

(define (term->string t)
  (with-output-to-string
    (λ ()
      (pretty-write t))))

(define (sort-types ts)
  (sort (remove-duplicates ts equal?)
        string<?
        #:key term->string))

(define (store-name->id name kind)
  (define s (symbol->string name))
  (define prefix
    (case kind
      [(Prompt) "tag"]
      [(Mark) "key"]
      [else
       (error 'store-name->id "unexpected kind ~s for ~s" kind name)]))
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

(define (ty->lean-jsexpr ty)
  (match ty
    ['Num '("Num")]
    ['String '("String")]
    ['Bool '("Bool")]
    ['Unit '("Unit")]
    [`(→ ,t1 ,t2)
     `("->" ,(ty->lean-jsexpr t1) ,(ty->lean-jsexpr t2))]
    [`(Prompt ,t1 ,t2)
     `("Prompt" ,(ty->lean-jsexpr t1) ,(ty->lean-jsexpr t2))]
    [`(Mark ,t)
     `("Mark" ,(ty->lean-jsexpr t))]
    [`(List ,t)
     `("List" ,(ty->lean-jsexpr t))]
    [`(Con ,t)
     `("Con" ,(ty->lean-jsexpr t))]
    [else
     (error 'ty->lean-jsexpr "unsupported type ~s" ty)]))

(define (lean-jsexpr->ty jsexpr)
  (match jsexpr
    [(? void?) #f]
    ['null #f]
    ['("Num") 'Num]
    ['("String") 'String]
    ['("Bool") 'Bool]
    ['("Unit") 'Unit]
    [`("->" ,t1 ,t2)
     `(→ ,(lean-jsexpr->ty t1) ,(lean-jsexpr->ty t2))]
    [`("Prompt" ,t1 ,t2)
     `(Prompt ,(lean-jsexpr->ty t1) ,(lean-jsexpr->ty t2))]
    [`("Mark" ,t)
     `(Mark ,(lean-jsexpr->ty t))]
    [`("List" ,t)
     `(List ,(lean-jsexpr->ty t))]
    [`("Con" ,t)
     `(Con ,(lean-jsexpr->ty t))]
    [else
     (error 'lean-jsexpr->ty "unexpected Lean type ~s" jsexpr)]))

(define (store-types->lean-symbol-table store-types)
  (for/hash ([binding (in-list store-types)])
    (match-define (list name ty) binding)
    (values name ty)))

(define (symbol->lean-expr x store-table)
  (cond
    [(hash-has-key? store-table x)
     (match (hash-ref store-table x)
       [`(Prompt ,_ ,_)
        `("tag" ,(store-name->id x 'Prompt))]
       [`(Mark ,_)
        `("key" ,(store-name->id x 'Mark))]
       [else
        (error 'symbol->lean-expr
               "unsupported store binding ~s for ~s"
               (hash-ref store-table x)
               x)])]
    [else
     `("var" ,(symbol->string x))]))

(define (mark-frame->lean-jsexpr w store-table)
  (for/list ([frame (in-list w)])
    (match frame
      [`(,mk ,v)
       (list (expr->lean-jsexpr mk store-table)
             (expr->lean-jsexpr v store-table))]
      [else
       (error 'mark-frame->lean-jsexpr "unexpected frame ~s" frame)])))

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
     #:when (memq op '(not zero? number? unit? boolean? procedure? prompt-tag? string-length))
     `("unop" ,(symbol->string op) ,(expr->lean-jsexpr e1 store-table))]
    [`(- ,e1)
     `("unop" "neg" ,(expr->lean-jsexpr e1 store-table))]
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
    [`(let ([(,x : ,t0) ,e1]) ,e2)
     (expr->lean-jsexpr `((λ (,x : ,t0) ,e2) ,e1) store-table)]
    [`(,e1 ,e2)
     `("app"
       ,(expr->lean-jsexpr e1 store-table)
       ,(expr->lean-jsexpr e2 store-table))]
    [else
     (error 'expr->lean-jsexpr "unsupported expression ~s" e)]))

(define (store-types->lean-store-typing store-types)
  (define tags
    (for/list ([binding (in-list store-types)])
      (match binding
        [(list name `(Prompt ,t1 ,t2))
         (list (store-name->id name 'Prompt)
               (ty->lean-jsexpr t1)
               (ty->lean-jsexpr t2))]
        [_ #f])))
  (define keys
    (for/list ([binding (in-list store-types)])
      (match binding
        [(list name `(Mark ,t))
         (list (store-name->id name 'Mark)
               (ty->lean-jsexpr t))]
        [_ #f])))
  (hasheq 'tags (filter values tags)
          'keys (filter values keys)))

(define (store-types->redex-store store-types)
  (for/fold ([σ '·])
            ([binding (in-list (reverse store-types))])
    (match-define (list name _ty) binding)
    `(,name ,σ)))

(define (redex-store->lean-store σ)
  (let loop ([σ σ] [tags '()] [keys '()])
    (match σ
      ['·
       (hasheq 'tags (reverse tags)
               'keys (reverse keys))]
      [`(,name ,rest)
       (define s (symbol->string name))
       (cond
         [(regexp-match? #rx"^tag([0-9]+)?$" s)
          (loop rest (cons (store-name->id name 'Prompt) tags) keys)]
         [(regexp-match? #rx"^key([0-9]+)?$" s)
          (loop rest tags (cons (store-name->id name 'Mark) keys))]
         [else
          (error 'redex-store->lean-store "unexpected store name ~s" name)])]
      [else
       (error 'redex-store->lean-store "unexpected store ~s" σ)])))

(define (redex-final-program expr store-types)
  (define σ (store-types->redex-store store-types))
  (define results
    (apply-reduction-relation*
     abort-red
     (term (<> ,expr ,σ))))
  (unless (= (length results) 1)
    (error 'redex-final-program
           "expected one final Redex program, got ~a for term:\n~a"
           (length results)
           (term->string expr)))
  (match (car results)
    [`(<> ,e-final ,σ-final)
     (values e-final σ-final)]
    [other
     (error 'redex-final-program "unexpected Redex result ~s" other)]))

(define (source-value-like? e)
  (match e
    [(? number?) #t]
    [(? boolean?) #t]
    ['unit #t]
    [(? symbol?) #t]
    [`(λ (,x : ,_t) ,body) #t]
    [`(null ,_t) #t]
    [`(cons ,e1 ,e2)
     (and (source-value-like? e1)
          (source-value-like? e2))]
    [_ #f]))

(define (soundness-query->lean-jsexpr sample)
  (define store-table
    (store-types->lean-symbol-table (typing-sample-store-types sample)))
  (hasheq 'env '()
          'storeTyping (store-types->lean-store-typing
                        (typing-sample-store-types sample))
          'expr (expr->lean-jsexpr (typing-sample-expr sample) store-table)
          'store (redex-store->lean-store
                  (store-types->redex-store (typing-sample-store-types sample)))))

(define (lean-run-soundness-batch queries
                                  #:fuel [fuel 2000]
                                  #:timeout [timeout-seconds 30])
  (define request
    (hasheq 'fuel fuel
            'queries queries))
  (define-values (proc stdout stdin stderr)
    (parameterize ([current-directory project-root])
      (apply subprocess
             #f
             #f
             #f
             (lean-soundness-command))))
  (display (jsexpr->string request) stdin)
  (close-output-port stdin)
  (define done? (sync/timeout timeout-seconds proc))
  (unless done?
    (subprocess-kill proc #t)
    (error 'lean-run-soundness-batch
           "Lean soundness runner timed out after ~a seconds"
           timeout-seconds))
  (subprocess-wait proc)
  (define out (port->string stdout))
  (define err (port->string stderr))
  (unless (zero? (subprocess-status proc))
    (error 'lean-run-soundness-batch
           (string-append
            (format "Lean soundness runner failed with status ~a\n"
                    (subprocess-status proc))
            (if (string=? err "")
                ""
                (format "stderr:\n~a" err))
            (if (string=? out "")
                ""
                (format "stdout:\n~a" out)))))
  (define response (string->jsexpr out))
  (unless (list? response)
    (error 'lean-run-soundness-batch
           "expected JSON list from Lean, got ~s"
           response))
  response)

(define (walk-term e f)
  (f e)
  (match e
    [`(λ (,x : ,ty) ,body)
     (walk-term body f)]
    [`(if ,e1 ,e2 ,e3)
     (walk-term e1 f)
     (walk-term e2 f)
     (walk-term e3 f)]
    [`(,op ,e1 ,e2)
     #:when (memq op '(+ - * cons))
     (walk-term e1 f)
     (walk-term e2 f)]
    [`(,op ,e1)
     #:when (memq op '(- not zero? number? unit? boolean?))
     (walk-term e1 f)]
    [`(case ,e1 (null = ,e2) ((cons ,x1 ,x2) = ,e3))
     (walk-term e1 f)
     (walk-term e2 f)
     (walk-term e3 f)]
    [`(% ,e1 ,e2 ,e3)
     (walk-term e1 f)
     (walk-term e2 f)
     (walk-term e3 f)]
    [`(abort ,_t ,e1 ,e2)
     (walk-term e1 f)
     (walk-term e2 f)]
    [`(call/comp ,e1 ,e2)
     (walk-term e1 f)
     (walk-term e2 f)]
    [`(call/cm ,e1 ,e2 ,e3)
     (walk-term e1 f)
     (walk-term e2 f)
     (walk-term e3 f)]
    [`(ccm ,e1 ,_t)
     (walk-term e1 f)]
    [`(wcm ,w ,body)
     (for ([frame (in-list w)])
       (match frame
         [`(,mk ,v)
          (walk-term mk f)
          (walk-term v f)]))
     (walk-term body f)]
    [`(let ([(,x : ,_ty) ,e1]) ,e2)
     (walk-term e1 f)
     (walk-term e2 f)]
    [`(,e1 ,e2)
     (walk-term e1 f)
     (walk-term e2 f)]
    [_ (void)]))

(define soundness-constructs
  '(if λ case cons % abort call/comp call/cm ccm wcm make-prompt-tag make-cm-key))

(define (update-coverage! coverage e)
  (walk-term
   e
   (λ (node)
     (define hit
       (match node
         [`(λ ,_ ...) 'λ]
         [`(if ,_ ...) 'if]
         [`(case ,_ ...) 'case]
         [`(cons ,_ ...) 'cons]
         [`(% ,_ ...) '%]
         [`(abort ,_ ...) 'abort]
         [`(call/comp ,_ ...) 'call/comp]
         [`(call/cm ,_ ...) 'call/cm]
         [`(ccm ,_ ...) 'ccm]
         [`(wcm ,_ ...) 'wcm]
         [`(make-prompt-tag ,_ ...) 'make-prompt-tag]
         [`(make-cm-key ,_ ...) 'make-cm-key]
         [_ #f]))
     (when hit
       (hash-update! coverage hit add1 0)))))

(define (coverage-summary coverage)
  (for/list ([name (in-list soundness-constructs)])
    (list name (hash-ref coverage name 0))))

(define (scale-campaigns campaigns count)
  (for/list ([camp (in-list campaigns)])
    (campaign (campaign-name camp)
              count
              (campaign-generator camp))))

(define default-main-soundness-campaigns
  (scale-campaigns well-typed-main-campaigns 10))

(define default-test-soundness-campaigns
  (scale-campaigns well-typed-test-campaigns 3))

(define (check-redex-soundness! sample)
  (define expr (typing-sample-expr sample))
  (define store-types (typing-sample-store-types sample))
  (define initial-types (sort-types (redex-types expr store-types)))
  (unless (= (length initial-types) 1)
    (error 'check-redex-soundness!
           "expected exactly one initial type for ~a, got ~s\nterm:\n~a"
           (typing-sample-label sample)
           initial-types
           (term->string expr)))
  (define initial-type (car initial-types))
  (define-values (final-expr final-store) (redex-final-program expr store-types))
  (unless (source-value-like? final-expr)
    (error 'check-redex-soundness!
           "final Redex expression is not a source value for ~a\nfinal:\n~a\nstore:\n~a"
           (typing-sample-label sample)
           (term->string final-expr)
           (term->string final-store)))
  (define final-types (sort-types (redex-types final-expr store-types)))
  (unless (equal? final-types (list initial-type))
    (error 'check-redex-soundness!
           (string-append
            (format "~a Redex preservation mismatch\n" (typing-sample-label sample))
            (format "initial type: ~s\n" initial-type)
            (format "final types: ~s\n" final-types)
            (format "initial term:\n~a" (term->string expr))
            (format "final term:\n~a" (term->string final-expr))
            (format "final store:\n~a" (term->string final-store)))))
  initial-type)

(define (check-lean-soundness! sample initial-type lean-result)
  (define status (hash-ref lean-result 'status))
  (define lean-initial (lean-jsexpr->ty (hash-ref lean-result 'initialType)))
  (define lean-final (lean-jsexpr->ty (hash-ref lean-result 'finalType)))
  (unless (equal? status "preserved")
    (error 'check-lean-soundness!
           "Lean soundness failed for ~a\nstatus: ~a\ninitial: ~s\nfinal: ~s\nterm:\n~a"
           (typing-sample-label sample)
           status
           lean-initial
           lean-final
           (term->string (typing-sample-expr sample))))
  (unless (and (equal? lean-initial initial-type)
               (equal? lean-final initial-type))
    (error 'check-lean-soundness!
           "Lean soundness types disagreed for ~a\nexpected: ~s\nlean initial: ~s\nlean final: ~s\nterm:\n~a"
           (typing-sample-label sample)
           initial-type
           lean-initial
           lean-final
           (term->string (typing-sample-expr sample)))))

(define (run-soundness-checks! #:campaigns [campaigns default-main-soundness-campaigns]
                               #:seed [seed 20260322]
                               #:verbose? [verbose? #t])
  (define coverage (make-hash))
  (define start (current-inexact-milliseconds))
  (define samples
    (build-typing-samples #:campaigns campaigns
                          #:seed seed
                          #:deterministic well-typed-deterministic-samples
                          #:verbose? verbose?
                          #:coverage coverage))
  (define lean-results
    (lean-run-soundness-batch
     (for/list ([sample (in-list samples)])
       (soundness-query->lean-jsexpr sample))))
  (for ([sample (in-list samples)]
        [lean-result (in-list lean-results)])
    (define initial-type (check-redex-soundness! sample))
    (check-lean-soundness! sample initial-type lean-result))
  (define elapsed-ms (- (current-inexact-milliseconds) start))
  (when verbose?
    (printf "seed: ~a\n" seed)
    (printf "elapsed: ~a ms\n" (inexact->exact (round elapsed-ms)))
    (printf "samples: ~a\n" (length samples))
    (printf "coverage:\n")
    (for ([row (in-list (coverage-summary coverage))])
      (match-define (list name count) row)
      (printf "  ~a: ~a\n" name count)))
  coverage)

(module+ test
  (define coverage
    (run-soundness-checks! #:campaigns default-test-soundness-campaigns
                           #:seed 20260322
                           #:verbose? #f))
  (for ([name (in-list soundness-constructs)])
    (check-true
     (positive? (hash-ref coverage name 0))
     (format "expected soundness coverage for ~a" name))))

(module+ main
  (run-soundness-checks!))
