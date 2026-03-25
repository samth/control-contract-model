#lang racket

(require json
         racket/list
         racket/match
         racket/pretty
         racket/runtime-path
         racket/string
         rackunit
         redex/reduction-semantics
         (except-in "model.rkt" let))

(provide redex-types
         lean-types
         typed-racket-typechecks?
         (struct-out campaign)
         (struct-out typing-sample)
         build-typing-samples
         well-typed-deterministic-samples
         well-typed-main-campaigns
         well-typed-test-campaigns
         compare-typing!
         run-random-typing-checks!)

(struct tr-result (ok? message) #:transparent)
(struct campaign (name count generator) #:transparent)
(struct typing-sample (label expr store-types) #:transparent)

(define-runtime-path model-dir ".")
(define project-root
  (simplify-path (build-path model-dir 'up)))
(define lean-typechecker-path
  (simplify-path
   (build-path project-root "RequestProject" "TSTH" "TypecheckerMain.lean")))
(define built-lean-typechecker-path
  (simplify-path
   (build-path project-root ".lake" "build" "bin" "tsth-typechecker")))

(define typing-constructs
  '(if
    λ
    case
    cons
    %
    abort
    call/comp
    call/cm
    ccm
    wcm
    make-prompt-tag
    make-cm-key))

;; Compare only against the model's type vocabulary. Typed Racket also has
;; truthiness and richer union/occurrence typing that the Redex judgment
;; does not try to express.
(define model-type-candidates
  '(Num
    Bool
    Unit
    (List Num)
    (List Bool)
    (List Unit)
    (→ Num Num)
    (→ Bool Bool)
    (→ Unit Unit)
    (Mark Num)
    (Mark Bool)
    (Mark Unit)
    (Prompt Num Num)
    (Prompt Bool Bool)
    (Prompt Unit Unit)))

(define default-lean-typechecker-command
  (if (file-exists? built-lean-typechecker-path)
      (list (path->string built-lean-typechecker-path))
      (list (or (find-executable-path "lake") "lake")
            "env"
            "lean"
            "--run"
            (path->string lean-typechecker-path))))

(define (lean-typechecker-command)
  (if (getenv "TSTH_LEAN_TYPECHECKER")
      (list (getenv "TSTH_LEAN_TYPECHECKER"))
      default-lean-typechecker-command))

(define (lean-typechecker-available?)
  (or (getenv "TSTH_LEAN_TYPECHECKER")
      (find-executable-path "lake")))

(define (random-small-int)
  (- (random 11) 5))

(define (random-base-type)
  (list-ref '(Num Bool Unit) (random 3)))

(define (random-list-elem-type)
  (list-ref '(Num Bool Unit) (random 3)))

(define (term->string t)
  (with-output-to-string
    (λ ()
      (pretty-write t))))

(define (store-types->redex-store-type store-types)
  (for/fold ([Σ '·])
            ([binding (in-list (reverse store-types))])
    (match-define (list name ty) binding)
    `(,name : ,ty ,Σ)))

(define (redex-types e [store-types '()])
  (remove-duplicates
   (judgment-holds (tc · ,(store-types->redex-store-type store-types) ,e t) t)
   equal?))

(define (ty->typed-racket ty)
  (match ty
    ['Num 'Integer]
    ['Bool 'Boolean]
    ['Unit 'Void]
    [`(→ ,t1 ,t2)
     `(-> ,(ty->typed-racket t1)
          ,(ty->typed-racket t2))]
    [`(Prompt ,t1 ,t2)
     `(Prompt-Tagof ,(ty->typed-racket t2)
                    (-> ,(ty->typed-racket t1)
                        ,(ty->typed-racket t2)))]
    [`(Mark ,t)
     `(Continuation-Mark-Keyof ,(ty->typed-racket t))]
    [`(List ,t)
     `(Listof ,(ty->typed-racket t))]
    [else
     (error 'ty->typed-racket "unsupported type ~s" ty)]))

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

(define (type-query->lean-jsexpr expr store-types)
  (define store-table (store-types->lean-symbol-table store-types))
  (hasheq 'env '()
          'storeTyping (store-types->lean-store-typing store-types)
          'expr (expr->lean-jsexpr expr store-table)
          'candidates (map ty->lean-jsexpr model-type-candidates)))

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

(define (lean-run-batch queries #:timeout [timeout-seconds 30])
  (unless (lean-typechecker-available?)
    (error 'lean-run-batch "Lean typechecker runner unavailable"))
  (define request
    (hasheq 'queries queries))
  (define-values (proc stdout stdin stderr)
    (parameterize ([current-directory project-root])
      (apply subprocess
             #f
             #f
             #f
             (lean-typechecker-command))))
  (display (jsexpr->string request) stdin)
  (close-output-port stdin)
  (define done? (sync/timeout timeout-seconds proc))
  (unless done?
    (subprocess-kill proc #t)
    (error 'lean-run-batch
           "Lean typechecker timed out after ~a seconds"
           timeout-seconds))
  (subprocess-wait proc)
  (define out (port->string stdout))
  (define err (port->string stderr))
  (unless (zero? (subprocess-status proc))
    (error 'lean-run-batch
           (string-append
            (format "Lean typechecker failed with status ~a\n"
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

(define (lean-types/batch samples #:timeout [timeout-seconds 30] #:batch-size [batch-size 500])
  (if (not (lean-typechecker-available?))
      #f
      (append-map
       (λ (chunk)
         (define queries
           (for/list ([sample (in-list chunk)])
             (type-query->lean-jsexpr (typing-sample-expr sample)
                                      (typing-sample-store-types sample))))
         (for/list ([result (in-list (lean-run-batch queries #:timeout timeout-seconds))])
           (sort-types (map lean-jsexpr->ty result))))
       (chunk-list samples batch-size))))

(define (lean-types expr [store-types '()])
  (define sample (typing-sample 'lean-single expr store-types))
  (define result (lean-types/batch (list sample)))
  (and result (car result)))

(define (wcm->typed-racket w body)
  (match w
    ['() body]
    [`((,mk ,v) ,rest ...)
     `(with-continuation-mark
        ,(expr->typed-racket mk)
        ,(expr->typed-racket v)
        ,(wcm->typed-racket rest body))]
    [else
     (error 'wcm->typed-racket "unexpected mark frame ~s" w)]))

(define (expr->typed-racket e)
  (match e
    [(? number?) e]
    [(? boolean?) e]
    ['unit '(void)]
    [(? symbol?) e]
    [`(λ (,x : ,ty) ,body)
     `(lambda ([,x : ,(ty->typed-racket ty)])
        ,(expr->typed-racket body))]
    [`(if ,e1 ,e2 ,e3)
     `(if ,(expr->typed-racket e1)
          ,(expr->typed-racket e2)
          ,(expr->typed-racket e3))]
    [`(+ ,e1 ,e2)
     `(+ ,(expr->typed-racket e1)
         ,(expr->typed-racket e2))]
    [`(- ,e1 ,e2)
     `(- ,(expr->typed-racket e1)
         ,(expr->typed-racket e2))]
    [`(* ,e1 ,e2)
     `(* ,(expr->typed-racket e1)
         ,(expr->typed-racket e2))]
    [`(- ,e1)
     `(- ,(expr->typed-racket e1))]
    [`(not ,e1)
     `(not ,(expr->typed-racket e1))]
    [`(zero? ,e1)
     `(zero? ,(expr->typed-racket e1))]
    [`(number? ,e1)
     `(number? ,(expr->typed-racket e1))]
    [`(unit? ,e1)
     `(void? ,(expr->typed-racket e1))]
    [`(boolean? ,e1)
     `(boolean? ,(expr->typed-racket e1))]
    [`(cons ,e1 ,e2)
     `(cons ,(expr->typed-racket e1)
            ,(expr->typed-racket e2))]
    [`(null ,ty)
     `(ann null ,(ty->typed-racket `(List ,ty)))]
    [`(case ,scrutinee
        (null = ,null-branch)
        ((cons ,x1 ,x2) = ,cons-branch))
     (define tmp (gensym 'lst))
     `(let ([,tmp ,(expr->typed-racket scrutinee)])
        (if (null? ,tmp)
            ,(expr->typed-racket null-branch)
            (let ([,x1 (car ,tmp)]
                  [,x2 (cdr ,tmp)])
              ,(expr->typed-racket cons-branch))))]
    [`(make-prompt-tag ,t1 ,t2)
     `((inst make-continuation-prompt-tag
             ,(ty->typed-racket t2)
             (-> ,(ty->typed-racket t1)
                 ,(ty->typed-racket t2))))]
    [`(make-cm-key ,t)
     `((inst make-continuation-mark-key
             ,(ty->typed-racket t)))]
    [`(% ,e1 ,e2 ,handler)
     `(call-with-continuation-prompt
       (lambda () ,(expr->typed-racket e1))
       ,(expr->typed-racket e2)
       ,(expr->typed-racket handler))]
    [`(abort ,_t ,e1 ,e2)
     `(abort-current-continuation
       ,(expr->typed-racket e1)
       ,(expr->typed-racket e2))]
    [`(call/comp ,e1 ,e2)
     `(call-with-composable-continuation
       ,(expr->typed-racket e1)
       ,(expr->typed-racket e2))]
    [`(call/cm ,e1 ,e2 ,e3)
     `(with-continuation-mark
        ,(expr->typed-racket e1)
        ,(expr->typed-racket e2)
        ,(expr->typed-racket e3))]
    [`(ccm ,e1 ,t)
     `(ann
       (continuation-mark-set->list
        (current-continuation-marks)
        ,(expr->typed-racket e1))
       ,(ty->typed-racket `(List ,t)))]
    [`(wcm ,w ,body)
     (wcm->typed-racket w (expr->typed-racket body))]
    [`(let ([(,x : ,ty) ,e1]) ,e2)
     `((lambda ([,x : ,(ty->typed-racket ty)])
         ,(expr->typed-racket e2))
       ,(expr->typed-racket e1))]
    [`(,e1 ,e2)
     `(,(expr->typed-racket e1)
       ,(expr->typed-racket e2))]
    [else
     (error 'expr->typed-racket "unsupported expression ~s" e)]))

(define (make-typed-racket-namespace)
  (make-base-namespace))

(define (store-binding->typed-racket-defs binding)
  (match-define (list name ty) binding)
  (match ty
    [`(Mark ,inner-ty)
     `((: ,name ,(ty->typed-racket ty))
       (define ,name
         ((inst make-continuation-mark-key
                ,(ty->typed-racket inner-ty)))))]
    [`(Prompt ,t1 ,t2)
     `((: ,name ,(ty->typed-racket ty))
       (define ,name
         ((inst make-continuation-prompt-tag
                ,(ty->typed-racket t2)
                (-> ,(ty->typed-racket t1)
                    ,(ty->typed-racket t2))))))]
    [else
     (error 'store-binding->typed-racket-defs
            "unsupported store binding ~s"
            binding)]))

(define (run-typed-racket-module! ns expr [expected-ty #f] [store-types '()])
  (define module-name (gensym 'typing-check))
  (define module-form
    `(module ,module-name typed/racket/base
       ,@(append-map store-binding->typed-racket-defs store-types)
       ,@(if expected-ty
             `((: result ,(ty->typed-racket expected-ty))
               (define result ,(expr->typed-racket expr)))
             `((define result ,(expr->typed-racket expr))))))
  (with-handlers ([exn:fail?
                   (λ (e)
                     (tr-result #f (exn-message e)))])
    (parameterize ([current-namespace ns])
      (call-with-output-string
       (λ (out)
         (parameterize ([current-error-port out])
           (eval module-form)
           (namespace-require `(quote ,module-name))))))
    (tr-result #t #f)))

(define (typed-racket-typechecks? ns expr [expected-ty #f] [store-types '()])
  (tr-result-ok? (run-typed-racket-module! ns expr expected-ty store-types)))

(define (sort-types ts)
  (sort (remove-duplicates ts equal?)
        string<?
        #:key term->string))

(define (typed-racket-model-types ns expr [store-types '()])
  (for/list ([ty (in-list model-type-candidates)]
             #:when (typed-racket-typechecks? ns expr ty store-types))
    ty))

(define (compare-typing! ns label expr
                         #:store-types [store-types '()]
                         #:lean-types [lean-ts #f])
  (define redex-ts (sort-types (redex-types expr store-types)))
  (define typed-racket-ts
    (sort-types (typed-racket-model-types ns expr store-types)))
  (unless (and (equal? redex-ts typed-racket-ts)
               (or (not lean-ts)
                   (equal? redex-ts lean-ts)))
    (define bare-result (run-typed-racket-module! ns expr #f store-types))
    (error 'compare-typing!
           (string-append
            (format "~a typing mismatch\n" label)
            (format "redex: ~s\n" redex-ts)
            (format "typed-racket(model-types): ~s\n" typed-racket-ts)
            (if lean-ts
                (format "lean(model-types): ~s\n" lean-ts)
                "")
            (format "typed-racket(bare): ~a\n"
                    (if (tr-result-ok? bare-result)
                        'accepted
                        'type-error))
            (if (tr-result-ok? bare-result)
                ""
                (format "typed-racket error:\n~a\n"
                        (tr-result-message bare-result)))
            (if (null? store-types)
                ""
                (string-append
                 "store-types:\n"
                 (term->string store-types)))
            "term:\n"
            (term->string expr)))))

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
  (for/list ([name (in-list typing-constructs)])
    (list name (hash-ref coverage name 0))))

(define (random-list-value ty len)
  (for/fold ([tail `(null ,ty)])
            ([i (in-range len)])
    `(cons ,(case ty
              [(Num) (random-small-int)]
              [(Bool) (zero? (random 2))]
              [else 'unit])
           ,tail)))

(define (gen-typed-num-term)
  (case (random 7)
    [(0)
     (+ 1 (abs (random-small-int)))]
    [(1)
     `(+ ,(random-small-int) ,(random-small-int))]
    [(2)
     `((λ (x : Num) (+ x ,(random-small-int)))
       ,(random-small-int))]
    [(3)
     `((λ (xs : (List Num))
         (case xs
           (null = 0)
           ((cons x rest) = (+ x ,(random-small-int)))))
       ,(random-list-value 'Num (+ 1 (random 3))))]
    [(4)
     `((λ (pt : (Prompt Num Num))
         (% (abort Num pt ,(random-small-int))
            pt
            (λ (x : Num) (+ x ,(random-small-int)))))
       (make-prompt-tag Num Num))]
    [(5)
     `((λ (mk : (Mark Num))
         (call/cm mk ,(random-small-int)
                  (+ ,(random-small-int)
                     (case (ccm mk Num)
                       (null = 0)
                       ((cons x xs) = x))))
       )
       (make-cm-key Num))]
    [else
     `((λ (pt : (Prompt Num Num))
         (% (+ ,(random-small-int)
               (call/comp
                (λ (kont : (→ Num Num))
                  (+ (kont ,(random-small-int))
                     (kont ,(random-small-int))))
                pt))
            pt
            (λ (x : Num) x)))
       (make-prompt-tag Num Num))]))

(define (gen-typed-bool-term)
  (case (random 6)
    [(0) (zero? (random 2))]
    [(1)
     `(zero? ,(random-small-int))]
    [(2)
     `(not ,(zero? (random 2)))]
    [(3)
     `((λ (x : Bool) (if x #f #t))
       ,(zero? (random 2)))]
    [(4)
     `(number? ,(gen-typed-num-term))]
    [else
     `(if ,(zero? (random 2))
          (zero? ,(random-small-int))
          (boolean? ,(gen-typed-bool-term)))]))

(define (gen-typed-fun-term)
  (case (random 3)
    [(0)
     `(λ (x : Num) (+ x ,(random-small-int)))]
    [(1)
     `(λ (x : Bool) (if x #f #t))]
    [else
     `(λ (x : Unit) unit)]))

(define (gen-typed-list-term)
  (define ty (random-list-elem-type))
  (case (random 4)
    [(0) `(null ,ty)]
    [(1) (random-list-value ty (+ 1 (random 3)))]
    [(2)
     `((λ (mk : (Mark ,ty))
         (call/cm mk
                  ,(case ty
                     [(Num) (random-small-int)]
                     [(Bool) (zero? (random 2))]
                     [else 'unit])
                  (ccm mk ,ty)))
       (make-cm-key ,ty))]
    [else
     `((λ (xs : (List ,ty))
         (case xs
           (null = xs)
           ((cons x rest) = rest)))
       ,(random-list-value ty (+ 1 (random 3))))]))

(define (gen-typed-wcm-term)
  (define outer (random-small-int))
  (define inner (random-small-int))
  (vector
   `((λ (f : (→ Unit (List Num)))
       (wcm ((key0 ,outer)) (f unit)))
     (λ (x : Unit)
       (wcm ((key0 ,inner)) (ccm key0 Num))))
   '((key0 (Mark Num)))))

(define (gen-typed-call/comp-mark-term)
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

(define (gen-ill-typed-plus-term)
  `(+ #t ,(random-small-int)))

(define (gen-ill-typed-app-term)
  `((λ (x : Num) (+ x 1)) #t))

(define (gen-ill-typed-list-term)
  (if (zero? (random 2))
      `(cons 0 1)
      `((λ (xs : (List Num))
          (case ,(random-small-int)
            (null = 0)
            ((cons x rest) = x)))
        (null Num))))

(define (gen-ill-typed-prompt-term)
  (case (random 4)
    [(0)
     `(% 5 ,(random-small-int) (λ (x : Num) x))]
    [(1)
     `(% 5
         (make-prompt-tag Num Num)
         (λ (x : Bool) x))]
    [(2)
     `((λ (pt : (Prompt Num Num))
         (% #t pt (λ (x : Num) x)))
       (make-prompt-tag Num Num))]
    [else
     `((λ (pt : (Prompt Num Num))
         (abort Num pt #t))
       (make-prompt-tag Num Num))]))

(define (gen-ill-typed-call/comp-term)
  (case (random 3)
    [(0)
     `((λ (pt : (Prompt Num Num))
         (call/comp 0 pt))
       (make-prompt-tag Num Num))]
    [(1)
     `((λ (pt : (Prompt Num Num))
         (call/comp
          (λ (k : (→ Num Bool)) #t)
          pt))
       (make-prompt-tag Num Num))]
    [else
     `(call/comp
       (λ (k : (→ Num Num)) 0)
       ,(random-small-int))]))

(define (gen-ill-typed-mark-term)
  (case (random 4)
    [(0)
     `((λ (mk : (Mark Num))
         (call/cm mk #t 0))
       (make-cm-key Num))]
    [(1)
     `((λ (mk : (Mark Num))
         (ccm mk Bool))
       (make-cm-key Num))]
    [(2)
     `((λ (mk : (Mark Num))
         (wcm ((mk #t)) (ccm mk Num)))
       (make-cm-key Num))]
    [else
     `((λ (pt : (Prompt Num Num))
         (call/cm pt 0 1))
       (make-prompt-tag Num Num))]))

(define deterministic-samples
  (list
   (list 'typed-abort
         '((λ (pt : (Prompt Num Num))
             (% (abort Num pt 5)
                pt
                (λ (x : Num) (+ x 1))))
           (make-prompt-tag Num Num))
         '())
   (list 'typed-call/comp
         '((λ (pt : (Prompt Num Num))
             (% (+ 1
                   (call/comp
                    (λ (kont : (→ Num Num))
                      (+ (kont 3) (kont 5)))
                    pt))
                pt
                (λ (x : Num) x)))
           (make-prompt-tag Num Num))
         '())
   (list 'typed-mark
         '((λ (mk : (Mark Num))
             (call/cm mk 5 (ccm mk Num)))
           (make-cm-key Num))
         '())
   (list 'typed-wcm
         '((λ (f : (→ Unit (List Num)))
             (wcm ((key0 5)) (f unit)))
           (λ (x : Unit)
             (wcm ((key0 3)) (ccm key0 Num))))
         '((key0 (Mark Num))))
   (list 'ill-prompt
         '(% 5 0 (λ (x : Num) x))
         '())
   (list 'ill-mark
         '((λ (mk : (Mark Num))
             (call/cm mk #t 0))
           (make-cm-key Num))
         '())))

(define well-typed-deterministic-samples
  (list
   (list 'typed-abort
         '((λ (pt : (Prompt Num Num))
             (% (abort Num pt 5)
                pt
                (λ (x : Num) (+ x 1))))
           (make-prompt-tag Num Num))
         '())
   (list 'typed-call/comp
         '((λ (pt : (Prompt Num Num))
             (% (+ 1
                   (call/comp
                    (λ (kont : (→ Num Num))
                      (+ (kont 3) (kont 5)))
                    pt))
                pt
                (λ (x : Num) x)))
           (make-prompt-tag Num Num))
         '())
   (list 'typed-mark
         '((λ (mk : (Mark Num))
             (call/cm mk 5 (ccm mk Num)))
           (make-cm-key Num))
         '())
   (list 'typed-wcm
         '((λ (f : (→ Unit (List Num)))
             (wcm ((key0 5)) (f unit)))
           (λ (x : Unit)
             (wcm ((key0 3)) (ccm key0 Num))))
         '((key0 (Mark Num))))))

(define default-main-campaigns
  (list
   (campaign 'typed-num 80 gen-typed-num-term)
   (campaign 'typed-bool 50 gen-typed-bool-term)
   (campaign 'typed-fun 30 gen-typed-fun-term)
   (campaign 'typed-list 40 gen-typed-list-term)
   (campaign 'typed-wcm 40 gen-typed-wcm-term)
   (campaign 'typed-call/comp+marks 40 gen-typed-call/comp-mark-term)
   (campaign 'ill-plus 25 gen-ill-typed-plus-term)
   (campaign 'ill-app 25 gen-ill-typed-app-term)
   (campaign 'ill-list 25 gen-ill-typed-list-term)
   (campaign 'ill-prompt 40 gen-ill-typed-prompt-term)
   (campaign 'ill-call/comp 30 gen-ill-typed-call/comp-term)
   (campaign 'ill-mark 30 gen-ill-typed-mark-term)))

(define default-test-campaigns
  (list
   (campaign 'typed-num 12 gen-typed-num-term)
   (campaign 'typed-bool 8 gen-typed-bool-term)
   (campaign 'typed-fun 5 gen-typed-fun-term)
   (campaign 'typed-list 6 gen-typed-list-term)
   (campaign 'typed-wcm 6 gen-typed-wcm-term)
   (campaign 'typed-call/comp+marks 6 gen-typed-call/comp-mark-term)
   (campaign 'ill-plus 5 gen-ill-typed-plus-term)
   (campaign 'ill-app 5 gen-ill-typed-app-term)
   (campaign 'ill-list 5 gen-ill-typed-list-term)
   (campaign 'ill-prompt 6 gen-ill-typed-prompt-term)
   (campaign 'ill-call/comp 6 gen-ill-typed-call/comp-term)
   (campaign 'ill-mark 6 gen-ill-typed-mark-term)))

(define well-typed-main-campaigns
  (list
   (campaign 'typed-num 80 gen-typed-num-term)
   (campaign 'typed-bool 50 gen-typed-bool-term)
   (campaign 'typed-fun 30 gen-typed-fun-term)
   (campaign 'typed-list 40 gen-typed-list-term)
   (campaign 'typed-wcm 40 gen-typed-wcm-term)
   (campaign 'typed-call/comp+marks 40 gen-typed-call/comp-mark-term)))

(define well-typed-test-campaigns
  (list
   (campaign 'typed-num 12 gen-typed-num-term)
   (campaign 'typed-bool 8 gen-typed-bool-term)
   (campaign 'typed-fun 5 gen-typed-fun-term)
   (campaign 'typed-list 6 gen-typed-list-term)
   (campaign 'typed-wcm 6 gen-typed-wcm-term)
   (campaign 'typed-call/comp+marks 6 gen-typed-call/comp-mark-term)))

(define (normalize-sample label sample)
  (define-values (expr store-types)
    (match sample
      [(vector expr store-types)
       (values expr store-types)]
      [expr
       (values expr '())]))
  (typing-sample label expr store-types))

(define (build-typing-samples #:campaigns [campaigns default-main-campaigns]
                              #:seed [seed 20260321]
                              #:deterministic [deterministic deterministic-samples]
                              #:verbose? [verbose? #f]
                              #:coverage [coverage #f])
  (random-seed seed)
  (define samples '())
  (define (record-sample! sample)
    (set! samples (cons sample samples))
    (when coverage
      (update-coverage! coverage (typing-sample-expr sample))))
  (for ([entry (in-list deterministic)])
    (match-define (list label expr store-types) entry)
    (record-sample! (typing-sample label expr store-types)))
  (for ([camp (in-list campaigns)])
    (when verbose?
      (printf "campaign ~a: ~a samples\n"
              (campaign-name camp)
              (campaign-count camp)))
    (for ([i (in-range (campaign-count camp))])
      (record-sample!
       (normalize-sample (format "~a/~a" (campaign-name camp) i)
                         ((campaign-generator camp))))))
  (reverse samples))

(define (run-random-typing-checks! #:campaigns [campaigns default-main-campaigns]
                                   #:seed [seed 20260321]
                                    #:verbose? [verbose? #t])
  (random-seed seed)
  (define ns (make-typed-racket-namespace))
  (define coverage (make-hash))
  (define start (current-inexact-milliseconds))
  (define ordered-samples
    (build-typing-samples #:campaigns campaigns
                          #:seed seed
                          #:deterministic deterministic-samples
                          #:verbose? verbose?
                          #:coverage coverage))
  (define lean-results
    (and (lean-typechecker-available?)
         (lean-types/batch ordered-samples)))
  (for ([sample (in-list ordered-samples)]
        [lean-ts (in-list (or lean-results
                              (make-list (length ordered-samples) #f)))])
    (compare-typing! ns
                     (typing-sample-label sample)
                     (typing-sample-expr sample)
                     #:store-types (typing-sample-store-types sample)
                     #:lean-types lean-ts))
  (define elapsed-ms (- (current-inexact-milliseconds) start))
  (when verbose?
    (printf "seed: ~a\n" seed)
    (printf "elapsed: ~a ms\n" (inexact->exact (round elapsed-ms)))
    (printf "lean: ~a\n"
            (if lean-results
                'enabled
                'unavailable))
    (printf "coverage:\n")
    (for ([row (in-list (coverage-summary coverage))])
      (match-define (list name count) row)
      (printf "  ~a: ~a\n" name count)))
  coverage)

(module+ test
  (define coverage
    (run-random-typing-checks! #:campaigns default-test-campaigns
                               #:seed 20260321
                               #:verbose? #f))
  (for ([name (in-list '(% abort call/comp call/cm ccm wcm make-prompt-tag make-cm-key λ if cons case))])
    (check-true
     (positive? (hash-ref coverage name 0))
     (format "expected typing coverage for ~a" name))))

(module+ main
  (run-random-typing-checks!))
