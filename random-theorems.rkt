#lang racket

(require json
         racket/list
         racket/match
         racket/pretty
         racket/runtime-path
         rackunit
         redex/reduction-semantics
         (except-in "model.rkt" let)
         (prefix-in eval: "random.rkt")
         "random-soundness.rkt"
         "random-typing.rkt")

(provide run-theorem-random-checks!)

(define typed-label "τ")
(define untyped-label "υ")
(define blame-contract-label "j")

(define-runtime-path model-dir ".")
(define project-root
  (simplify-path (build-path model-dir 'up)))
(define lean-oracle-path
  (simplify-path
   (build-path project-root "RequestProject" "TSTH" "TestOracleMain.lean")))
(define lean-interpreter-path
  (simplify-path
   (build-path project-root "RequestProject" "TSTH" "Interpreter.lean")))
(define built-lean-oracle-path
  (simplify-path
   (build-path project-root ".lake" "build" "bin" "tsth-test-oracle")))

(define (built-lean-oracle-fresh?)
  (and (file-exists? built-lean-oracle-path)
       (>= (file-or-directory-modify-seconds built-lean-oracle-path)
           (max (file-or-directory-modify-seconds lean-oracle-path)
                (file-or-directory-modify-seconds lean-interpreter-path)))))

(define default-lean-oracle-command
  (if (built-lean-oracle-fresh?)
      (list (path->string built-lean-oracle-path))
      (list (or (find-executable-path "lake") "lake")
            "env"
            "lean"
            "--run"
            (path->string lean-oracle-path))))

(define (lean-oracle-command)
  (if (getenv "TSTH_LEAN_TEST_ORACLE")
      (list (getenv "TSTH_LEAN_TEST_ORACLE"))
      default-lean-oracle-command))

(define model-types
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

(define contract-flat-base-types
  '(Num Bool Unit))

(define fixed-mark-store-types
  '((key0 (Mark Num))
    (key1 (Mark Bool))
    (key2 (Mark Unit))))

(define (number?-contract)
  '(flat (λ (x : Num) (number? x))))

(define (zero?-contract)
  '(flat (λ (x : Num) (zero? x))))

(define (number->number-contract)
  `(-> ,(number?-contract) ,(number?-contract)))

(define (term->string t)
  (with-output-to-string
    (λ ()
      (pretty-write t))))

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
     (error 'lean-jsexpr->ty "unexpected type jsexpr ~s" jsexpr)]))

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
       (error 'store-name->id "cannot extract numeric id from ~s" name))
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
     #:when (memq op '(+ - * string-append))
     `("binop"
       ,(symbol->string op)
       ,(expr->lean-jsexpr e1 store-table)
       ,(expr->lean-jsexpr e2 store-table))]
    [`(,op ,e1)
     #:when (memq op '(- not zero? number? unit? boolean? procedure? prompt-tag? string-length))
     `("unop" ,(if (eq? op '-) "neg" (symbol->string op))
              ,(expr->lean-jsexpr e1 store-table))]
    [`(cons ,e1 ,e2)
     `("cons" ,(expr->lean-jsexpr e1 store-table)
               ,(expr->lean-jsexpr e2 store-table))]
    [`(null ,t0)
     `("null" ,(ty->lean-jsexpr t0))]
    [`(case ,scrutinee (null = ,null-branch) ((cons ,x1 ,x2) = ,cons-branch))
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
     `("wcm" ,(mark-frame->lean-jsexpr w store-table)
              ,(expr->lean-jsexpr body store-table))]
    [`(ccm ,e1 ,t0)
     `("ccm" ,(expr->lean-jsexpr e1 store-table) ,(ty->lean-jsexpr t0))]
    [`(call/comp ,e1 ,e2)
     `("call/comp" ,(expr->lean-jsexpr e1 store-table)
                    ,(expr->lean-jsexpr e2 store-table))]
    [`(call/cm ,e1 ,e2 ,e3)
     `("call/cm" ,(expr->lean-jsexpr e1 store-table)
                  ,(expr->lean-jsexpr e2 store-table)
                  ,(expr->lean-jsexpr e3 store-table))]
    [`(let ([(,x : ,t0) ,e1]) ,e2)
     (expr->lean-jsexpr `((λ (,x : ,t0) ,e2) ,e1) store-table)]
    [`(,e1 ,e2)
     `("app" ,(expr->lean-jsexpr e1 store-table)
              ,(expr->lean-jsexpr e2 store-table))]
    [else
     (error 'expr->lean-jsexpr "unsupported theorem-harness expr ~s" e)]))

(define (contract->lean-jsexpr ctc store-table)
  (match ctc
    [`(flat ,pred)
     `("flat" ,(expr->lean-jsexpr pred store-table))]
    [`(flatAnnot ,pred ,labels)
     `("flatAnnot" ,(expr->lean-jsexpr pred store-table) ,labels)]
    [`(-> ,ctc-a ,ctc-r)
     `("arr" ,(contract->lean-jsexpr ctc-a store-table)
              ,(contract->lean-jsexpr ctc-r store-table))]
    [`(prompt-tag/c ,ctc1 ,ctc2 ,_t1 ,_t2)
     `("prompt-tag/c" ,(contract->lean-jsexpr ctc1 store-table)
                      ,(contract->lean-jsexpr ctc2 store-table))]
    [`(mark/c ,inner ,_t)
     `("mark/c" ,(contract->lean-jsexpr inner store-table))]
    [`(list/c ,inner)
     `("list/c" ,(contract->lean-jsexpr inner store-table))]
    [else
     (error 'contract->lean-jsexpr "unsupported contract ~s" ctc)]))

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
  (define allocs
    (let loop ([σ σ])
      (match σ
        ['· '()]
        [`(,name ,rest)
         (define s (symbol->string name))
         (cons (cond
                 [(regexp-match? #rx"^tag([0-9]+)?$" s)
                  (list "tag" (store-name->id name 'Prompt))]
                 [(regexp-match? #rx"^key([0-9]+)?$" s)
                  (list "key" (store-name->id name 'Mark))]
                 [else
                  (error 'redex-store->lean-store "unexpected store name ~s" name)])
               (loop rest))]
        [else
         (error 'redex-store->lean-store "unexpected store ~s" σ)])))
  (hasheq 'allocs allocs))

(define (lean-store->redex-store jsexpr)
  (define allocs (hash-ref jsexpr 'allocs '()))
  (for/fold ([σ '·]) ([entry (in-list (reverse allocs))])
    (match entry
      [(list "tag" n)
       `(,(string->symbol (format "tag~a" n)) ,σ)]
      [(list "key" n)
       `(,(string->symbol (format "key~a" n)) ,σ)]
      [else
       (error 'lean-store->redex-store "unexpected store entry ~s" entry)])))

(define (lean-jsexpr->expr jsexpr)
  (match jsexpr
    [`("var" ,x) (string->symbol x)]
    [`("int" ,n) n]
    [`("bool" ,b) b]
    [`("string" ,s) s]
    ['("unit") 'unit]
    [`("lam" ,x ,t ,body)
     `(λ (,(string->symbol x) : ,(lean-jsexpr->ty t))
        ,(lean-jsexpr->expr body))]
    [`("null" ,t)
     `(null ,(lean-jsexpr->ty t))]
    [`("cons" ,e1 ,e2)
     `(cons ,(lean-jsexpr->expr e1) ,(lean-jsexpr->expr e2))]
    [`("tag" ,n)
     (string->symbol (format "tag~a" n))]
    [`("key" ,n)
     (string->symbol (format "key~a" n))]
    [`("app" ,e1 ,e2)
     `(,(lean-jsexpr->expr e1) ,(lean-jsexpr->expr e2))]
    [`("if" ,e1 ,e2 ,e3)
     `(if ,(lean-jsexpr->expr e1)
          ,(lean-jsexpr->expr e2)
          ,(lean-jsexpr->expr e3))]
    [`("mu" ,x ,t ,body)
     `(μ (,(string->symbol x) : ,(lean-jsexpr->ty t))
        ,(lean-jsexpr->expr body))]
    [`("unop" ,"neg" ,e1)
     `(- ,(lean-jsexpr->expr e1))]
    [`("unop" ,op ,e1)
     `(,(string->symbol op) ,(lean-jsexpr->expr e1))]
    [`("binop" ,op ,e1 ,e2)
     `(,(string->symbol op) ,(lean-jsexpr->expr e1) ,(lean-jsexpr->expr e2))]
    [`("case" ,e ,e-null ,x1 ,x2 ,e-cons)
     `(case ,(lean-jsexpr->expr e)
        (null = ,(lean-jsexpr->expr e-null))
        ((cons ,(string->symbol x1) ,(string->symbol x2)) = ,(lean-jsexpr->expr e-cons)))]
    [`("make-prompt-tag" ,t1 ,t2)
     `(make-prompt-tag ,(lean-jsexpr->ty t1) ,(lean-jsexpr->ty t2))]
    [`("make-cm-key" ,t0)
     `(make-cm-key ,(lean-jsexpr->ty t0))]
    [`("prompt" ,e1 ,e2 ,vh)
     `(% ,(lean-jsexpr->expr e1) ,(lean-jsexpr->expr e2) ,(lean-jsexpr->expr vh))]
    [`("abort" ,t0 ,pt ,v)
     `(abort ,(lean-jsexpr->ty t0)
             ,(lean-jsexpr->expr pt)
             ,(lean-jsexpr->expr v))]
    [`("wcm" ,w ,body)
     `(wcm ,(for/list ([frame (in-list w)])
              (match frame
                [(list mk v)
                 (list (lean-jsexpr->expr mk) (lean-jsexpr->expr v))]
                [else
                 (error 'lean-jsexpr->expr "unexpected frame ~s" frame)]))
           ,(lean-jsexpr->expr body))]
    [`("ccm" ,e1 ,t0)
     `(ccm ,(lean-jsexpr->expr e1) ,(lean-jsexpr->ty t0))]
    [`("call/comp" ,e1 ,e2)
     `(call/comp ,(lean-jsexpr->expr e1) ,(lean-jsexpr->expr e2))]
    [`("call/cm" ,e1 ,e2 ,e3)
     `(call/cm ,(lean-jsexpr->expr e1)
               ,(lean-jsexpr->expr e2)
               ,(lean-jsexpr->expr e3))]
    [else
     (error 'lean-jsexpr->expr "unexpected source expr ~s" jsexpr)]))

(define (lean-run-oracle-batch queries #:timeout [timeout-seconds 30])
  (define request (hasheq 'queries queries))
  (define-values (proc stdout stdin stderr)
    (parameterize ([current-directory project-root])
      (apply subprocess #f #f #f (lean-oracle-command))))
  (display (jsexpr->string request) stdin)
  (close-output-port stdin)
  (define done? (sync/timeout timeout-seconds proc))
  (unless done?
    (subprocess-kill proc #t)
    (error 'lean-run-oracle-batch
           "Lean theorem oracle timed out after ~a seconds"
           timeout-seconds))
  (subprocess-wait proc)
  (define out (port->string stdout))
  (define err (port->string stderr))
  (unless (zero? (subprocess-status proc))
    (error 'lean-run-oracle-batch
           (string-append
            (format "Lean theorem oracle failed with status ~a\n"
                    (subprocess-status proc))
            (if (string=? err "") "" (format "stderr:\n~a" err))
            (if (string=? out "") "" (format "stdout:\n~a" out)))))
  (define response (string->jsexpr out))
  (unless (list? response)
    (error 'lean-run-oracle-batch
           "expected JSON list from Lean oracle, got ~s"
           response))
  response)

(define (redex-contract-types c [store-types '()])
  (define Σ
    (for/fold ([Σ '·])
              ([binding (in-list (reverse store-types))])
      (match-define (list name ty) binding)
      `(,name : ,ty ,Σ)))
  (remove-duplicates
   (judgment-holds
    (tc · ,Σ ,c (Con t))
    t)
   equal?))

(define (predicate-for-type t [x 'x])
  (match (random 3)
    [0 `(number? ,x)]
    [1 `(unit? ,x)]
    [_ `(boolean? ,x)]))

(define (good-flat-contract t)
  (define x (gensym 'x))
  `(flat (λ (,x : ,t) ,(predicate-for-type t x))))

(define (bad-flat-contract t)
  (define x (gensym 'x))
  `(flat (λ (,x : ,t) 0)))

(define (random-model-type)
  (list-ref model-types (random (length model-types))))

(define (gen-random-contract depth)
  (define (single-contract-payload-type ctc)
    (match (redex-contract-types ctc)
      [(list t) t]
      [_ #f]))
  (if (zero? depth)
      (if (< (random 4) 3)
          (good-flat-contract
           (list-ref contract-flat-base-types
                     (random (length contract-flat-base-types))))
          (bad-flat-contract
           (list-ref contract-flat-base-types
                     (random (length contract-flat-base-types)))))
      (case (random 6)
        [(0) (good-flat-contract
              (list-ref contract-flat-base-types
                        (random (length contract-flat-base-types))))]
        [(1) (bad-flat-contract
              (list-ref contract-flat-base-types
                        (random (length contract-flat-base-types))))]
        [(2) `(-> ,(gen-random-contract (sub1 depth))
                   ,(gen-random-contract (sub1 depth)))]
        [(3) (define c1 (gen-random-contract (sub1 depth)))
             (define c2 (gen-random-contract (sub1 depth)))
             `(prompt-tag/c ,c1
                            ,c2
                            ,(or (single-contract-payload-type c1)
                                 (random-model-type))
                            ,(or (single-contract-payload-type c2)
                                 (random-model-type)))]
        [(4) (define inner (gen-random-contract (sub1 depth)))
             `(mark/c ,inner
                      ,(or (single-contract-payload-type inner)
                           (random-model-type)))]
        [else `(list/c ,(gen-random-contract (sub1 depth)))])))

(define (value-for-type t)
  (match t
    ['Num (random 7)]
    ['Bool (zero? (random 2))]
    ['Unit 'unit]
    ['String ""]
    [`(List ,elem)
     (if (zero? (random 2))
         `(null ,elem)
         `(cons ,(value-for-type elem) (null ,elem)))]
    [`(→ ,dom ,cod)
     (define x (gensym 'x))
     `(λ (,x : ,dom) ,(value-for-type cod))]
    [`(Prompt ,t1 ,t2)
     `(make-prompt-tag ,t1 ,t2)]
    [`(Mark ,t0)
     `(make-cm-key ,t0)]
    [else 0]))

(define (random-nonnegative-small-int)
  (random 7))

(define (gen-random-mark-frame)
  (define key-names '(key0 key1 key2 key9))
  (for/list ([i (in-range (add1 (random 3)))])
    (define mk
      (if (zero? (random 5))
          0
          (list-ref key-names (random (length key-names)))))
    (define expected-ty
      (match mk
        ['key0 'Num]
        ['key1 'Bool]
        ['key2 'Unit]
        [_ (random-model-type)]))
    (define v
      (if (< (random 4) 3)
          (value-for-type expected-ty)
          (value-for-type (random-model-type))))
    (list mk v)))

(define (gen-safe-flat-blame-term)
  (values `(monitor ,(number?-contract)
                    ,(random-nonnegative-small-int)
                    ,typed-label
                    ,untyped-label
                    ,blame-contract-label)
          '·))

(define (gen-safe-function-blame-term)
  (values `((monitor ,(number->number-contract)
                     (λ (x : Num) (+ x ,(random-nonnegative-small-int)))
                     ,typed-label
                     ,untyped-label
                     ,blame-contract-label)
            ,(random-nonnegative-small-int))
          '·))

(define (redex-list xs)
  (for/fold ([acc '(null Num)])
            ([x (in-list (reverse xs))])
    `(cons ,x ,acc)))

(define (gen-safe-list-blame-term)
  (define len (+ 1 (random 3)))
  (define xs (build-list len (λ (_) 0)))
  (values `(monitor (list/c ,(zero?-contract))
                    ,(redex-list xs)
                    ,typed-label
                    ,untyped-label
                    ,blame-contract-label)
          '·))

(define (gen-safe-mark-blame-term)
  (values `((λ (mk : (Mark Num))
              (call/cm mk 0 (ccm mk Num)))
            (monitor (mark/c ,(number?-contract) Num)
                     (make-cm-key Num)
                     ,typed-label
                     ,untyped-label
                     ,blame-contract-label))
          '·))

(define (gen-safe-prompt-blame-term)
  (values `((λ (pt : (Prompt Num Num))
              (% (abort Num pt 0)
                 pt
                 (λ (x : Num) (+ x 1))))
            (monitor (prompt-tag/c ,(zero?-contract) ,(number?-contract) Num Num)
                     (make-prompt-tag Num Num)
                     ,typed-label
                     ,untyped-label
                     ,blame-contract-label))
          '·))

(define blame-approximation-generators
  (vector gen-safe-flat-blame-term
          gen-safe-function-blame-term
          gen-safe-list-blame-term
          gen-safe-mark-blame-term
          gen-safe-prompt-blame-term))

(define (source-value-like? e)
  (match e
    [(? number?) #t]
    [(? boolean?) #t]
    [(? string?) #t]
    ['unit #t]
    [(? symbol?) #t]
    [`(λ (,x : ,_t) ,body) #t]
    [`(null ,_t) #t]
    [`(cons ,e1 ,e2)
     (and (source-value-like? e1)
          (source-value-like? e2))]
    [_ #f]))

(define (redex-reachable-within start target #:fuel [fuel 12])
  (let loop ([frontier (list start)]
             [seen (list start)]
             [remaining fuel])
    (cond
      [(member target seen equal?)
       (values #t seen)]
      [(or (zero? remaining) (null? frontier))
       (values #f seen)]
      [else
       (define next-frontier
         (for*/fold ([acc '()])
                    ([state (in-list frontier)]
                     [next (in-list (apply-reduction-relation abort-red state))]
                     #:unless (member next seen equal?))
           (cons next acc)))
       (define next-seen
         (append next-frontier seen))
       (loop next-frontier next-seen (sub1 remaining))])))

(define (typed-blame-answer? answer)
  (match answer
    [`(ctc-error ,k ,_) (equal? k typed-label)]
    [_ #f]))

(define (run-contract-correspondence! #:count [count 200]
                                      #:seed [seed 20260322]
                                      #:verbose? [verbose? #t])
  (random-seed seed)
  (define contracts
    (for/list ([i (in-range count)])
      (gen-random-contract 3)))
  (define responses
    (lean-run-oracle-batch
     (for/list ([ctc (in-list contracts)])
       (hasheq 'kind "contract-type"
               'env '()
               'storeTyping (hasheq 'tags '() 'keys '())
               'contract (contract->lean-jsexpr ctc #hash())))))
  (for ([ctc (in-list contracts)]
        [resp (in-list responses)])
    (define redex-types* (sort (redex-contract-types ctc) string<? #:key term->string))
    (define lean-type (lean-jsexpr->ty (hash-ref resp 'type)))
    (cond
      [(null? redex-types*)
       (unless (not lean-type)
         (error 'run-contract-correspondence!
                "Lean accepted ill-typed contract\ncontract:\n~a\nlean: ~s"
                (term->string ctc)
                lean-type))]
      [(= (length redex-types*) 1)
       (unless (equal? (car redex-types*) lean-type)
         (error 'run-contract-correspondence!
                "contract typing mismatch\ncontract:\n~a\nredex: ~s\nlean: ~s"
                (term->string ctc)
                redex-types*
                lean-type))]
      [else
       (error 'run-contract-correspondence!
              "contract had multiple Redex types: ~s\n~a"
              redex-types*
              (term->string ctc))]))
  (when verbose?
    (printf "contract correspondence: ~a samples\n" count)))

(define (run-mark-frame-correspondence! #:count [count 200]
                                        #:seed [seed 20260323]
                                        #:verbose? [verbose? #t])
  (random-seed seed)
  (define frames
    (for/list ([i (in-range count)])
      (gen-random-mark-frame)))
  (define responses
    (lean-run-oracle-batch
     (for/list ([w (in-list frames)])
       (hasheq 'kind "mark-frame"
               'env '()
               'storeTyping (store-types->lean-store-typing fixed-mark-store-types)
               'markFrame (mark-frame->lean-jsexpr w
                                                   (store-types->lean-symbol-table
                                                    fixed-mark-store-types))))))
  (for ([w (in-list frames)]
        [resp (in-list responses)])
    (define redex-ok?
      (equal? (redex-types `(wcm ,w unit) fixed-mark-store-types)
              '(Unit)))
    (define lean-ok? (hash-ref resp 'ok))
    (unless (equal? redex-ok? lean-ok?)
      (error 'run-mark-frame-correspondence!
             "mark-frame mismatch\nframe:\n~a\nredex: ~s\nlean: ~s"
             (term->string w)
             redex-ok?
             lean-ok?)))
  (when verbose?
    (printf "mark-frame correspondence: ~a samples\n" count)))

(define (run-step-correspondence! #:campaigns [campaigns well-typed-test-campaigns]
                                  #:seed [seed 20260324]
                                  #:verbose? [verbose? #t])
  (define samples
    (build-typing-samples #:campaigns campaigns
                          #:seed seed
                          #:deterministic well-typed-deterministic-samples
                          #:verbose? #f))
  (define queries
    (for/list ([sample (in-list samples)])
      (define store-types (typing-sample-store-types sample))
      (define store-table (store-types->lean-symbol-table store-types))
      (hasheq 'kind "step"
              'expr (expr->lean-jsexpr (typing-sample-expr sample) store-table)
              'store (redex-store->lean-store
                      (store-types->redex-store store-types)))))
  (define responses (lean-run-oracle-batch queries))
  (for ([sample (in-list samples)]
        [resp (in-list responses)])
    (define expr (typing-sample-expr sample))
    (define σ (store-types->redex-store (typing-sample-store-types sample)))
    (define initial-state `(<> ,expr ,σ))
    (define redex-steps
      (apply-reduction-relation abort-red initial-state))
    (unless (or (source-value-like? expr)
                (pair? redex-steps))
      (error 'run-step-correspondence!
             "progress-style failure on typed sample\nterm:\n~a\nstore:\n~a"
             (term->string expr)
             (term->string σ)))
    (define lean-next (hash-ref resp 'next))
    (when (and (pair? redex-steps)
               (eq? lean-next 'null))
      (error 'run-step-correspondence!
             "Redex can step but Lean machine returned terminal\nterm:\n~a\nstore:\n~a\nredex one-step:\n~a"
             (term->string expr)
             (term->string σ)
             (term->string redex-steps)))
    (unless (eq? lean-next 'null)
      (define lean-state
        `(<> ,(lean-jsexpr->expr (hash-ref lean-next 'expr))
             ,(lean-store->redex-store (hash-ref lean-next 'store))))
      (define-values (redex-reachable? redex-reachable)
        (redex-reachable-within initial-state lean-state))
      (unless redex-reachable?
        (error 'run-step-correspondence!
               (string-append
                "Lean step is not Redex-reachable\n"
                (format "label: ~a\n" (typing-sample-label sample))
                (format "initial:\n~a" (term->string initial-state))
                (format "lean next:\n~a" (term->string lean-state))
                (format "redex reachable count within budget: ~a\n"
                        (length redex-reachable)))))))
  (when verbose?
    (printf "step correspondence/progress approximation: ~a samples\n"
            (length samples))))

(define (lean-machine-state->redex-state jsexpr)
  (with-handlers ([exn:fail? (λ (_exn) #f)])
    (define reify (hash-ref jsexpr 'reify))
    `(<> ,(lean-jsexpr->expr (hash-ref reify 'expr))
         ,(lean-store->redex-store (hash-ref reify 'store)))))

(define (run-machine-trace-correspondence! #:campaigns [campaigns well-typed-test-campaigns]
                                           #:seed [seed 20260326]
                                           #:trace-fuel [trace-fuel 16]
                                           #:timeout [timeout-seconds 30]
                                           #:sample-limit [sample-limit #f]
                                           #:verbose? [verbose? #t])
  (define all-samples
    (build-typing-samples #:campaigns campaigns
                          #:seed seed
                          #:deterministic well-typed-deterministic-samples
                          #:verbose? #f))
  (define samples
    (if sample-limit
        (take all-samples (min sample-limit (length all-samples)))
        all-samples))
  (define queries
    (for/list ([sample (in-list samples)])
      (define store-types (typing-sample-store-types sample))
      (define store-table (store-types->lean-symbol-table store-types))
      (hasheq 'kind "machine-trace"
              'fuel trace-fuel
              'expr (expr->lean-jsexpr (typing-sample-expr sample) store-table)
              'store (redex-store->lean-store
                      (store-types->redex-store store-types)))))
  (define responses
    (lean-run-oracle-batch queries #:timeout timeout-seconds))
  (define unsupported-states 0)
  (define transition-misses 0)
  (define terminal-misses 0)
  (for ([sample (in-list samples)]
        [resp (in-list responses)])
    (define states (hash-ref resp 'states))
    (define timed-out? (hash-ref resp 'timedOut))
    (unless (list? states)
      (error 'run-machine-trace-correspondence!
             "expected state list from Lean machine trace, got ~s"
             states))
    (for ([state (in-list states)])
      (unless (hash-ref state 'machineWf)
        (error 'run-machine-trace-correspondence!
               "Lean reached a non-well-formed machine state\nlabel: ~a\nstate:\n~a"
               (typing-sample-label sample)
               (term->string state))))
    (for ([state (in-list states)]
          [next (in-list (rest states))])
      (define current-redex (lean-machine-state->redex-state state))
      (define next-redex (lean-machine-state->redex-state next))
      (cond
        [(and current-redex next-redex)
         (define-values (reachable? _reachable)
           (redex-reachable-within current-redex next-redex))
         (unless reachable?
           (set! transition-misses (add1 transition-misses)))]
        [else
         (set! unsupported-states (add1 unsupported-states))]))
    (unless timed-out?
      (define final-state (last states))
      (define final-redex (lean-machine-state->redex-state final-state))
      (define final-steps
        (and final-redex
             (apply-reduction-relation abort-red final-redex)))
      (cond
        [(not final-redex)
         (set! unsupported-states (add1 unsupported-states))]
        [(pair? final-steps)
         (set! terminal-misses (add1 terminal-misses))])))
  (when verbose?
    (printf "machine trace correspondence/WF approximation: ~a samples\n"
            (length samples))
    (printf "  unsupported runtime states: ~a\n" unsupported-states)
    (printf "  transition reachability misses: ~a\n" transition-misses)
    (printf "  terminal reducibility misses: ~a\n" terminal-misses)))

(define (run-blame-approximation! #:count [count 100]
                                  #:seed [seed 20260325]
                                  #:verbose? [verbose? #t])
  (random-seed seed)
  (for ([i (in-range count)])
    (define gen
      (vector-ref blame-approximation-generators
                  (random (vector-length blame-approximation-generators))))
    (define-values (term store) (gen))
    (define answer
      (eval:compare-term! term #:init-store store))
    (when (typed-blame-answer? answer)
      (error 'run-blame-approximation!
             "typed blame observed on mixed-language sample\nterm:\n~a\nanswer: ~s"
             (term->string term)
             answer)))
  (when verbose?
    (printf "blame approximation: ~a samples\n" count)))

(define (run-theorem-random-checks! #:typing-seed [typing-seed 20260321]
                                    #:soundness-seed [soundness-seed 20260322]
                                    #:contracts-seed [contracts-seed 20260322]
                                    #:frames-seed [frames-seed 20260323]
                                    #:steps-seed [steps-seed 20260324]
                                    #:machine-seed [machine-seed 20260326]
                                    #:machine-trace-fuel [machine-trace-fuel 16]
                                    #:machine-timeout [machine-timeout 30]
                                    #:machine-sample-limit [machine-sample-limit #f]
                                    #:blame-seed [blame-seed 20260325]
                                    #:contract-count [contract-count 200]
                                    #:frame-count [frame-count 200]
                                    #:blame-count [blame-count 100]
                                    #:verbose? [verbose? #t])
  (when verbose?
    (printf "typechecker expression correspondence:\n"))
  (run-random-typing-checks! #:campaigns well-typed-test-campaigns
                             #:seed typing-seed
                             #:verbose? verbose?)
  (when verbose?
    (printf "preservation approximation:\n"))
  (run-soundness-checks! #:campaigns default-test-soundness-campaigns
                         #:seed soundness-seed
                         #:verbose? verbose?)
  (when verbose?
    (printf "contract correspondence:\n"))
  (run-contract-correspondence! #:count contract-count
                                #:seed contracts-seed
                                #:verbose? verbose?)
  (when verbose?
    (printf "mark-frame correspondence:\n"))
  (run-mark-frame-correspondence! #:count frame-count
                                  #:seed frames-seed
                                  #:verbose? verbose?)
  (when verbose?
    (printf "step correspondence:\n"))
  (run-step-correspondence! #:campaigns well-typed-test-campaigns
                            #:seed steps-seed
                            #:verbose? verbose?)
  (when verbose?
    (printf "machine trace correspondence:\n"))
  (run-machine-trace-correspondence! #:campaigns well-typed-test-campaigns
                                     #:seed machine-seed
                                     #:trace-fuel machine-trace-fuel
                                     #:timeout machine-timeout
                                     #:sample-limit machine-sample-limit
                                     #:verbose? verbose?)
  (when verbose?
    (printf "blame approximation:\n"))
  (run-blame-approximation! #:count blame-count
                            #:seed blame-seed
                            #:verbose? verbose?)
  (when verbose?
    (printf "mixed-language stress approximation:\n"))
  (eval:run-random-suite! #:evaluation-campaigns eval:default-test-campaigns
                          #:soundness-campaigns default-test-soundness-campaigns
                          #:seed soundness-seed
                          #:verbose? verbose?))

(module+ test
  (run-theorem-random-checks! #:contract-count 40
                              #:frame-count 40
                              #:blame-count 40
                              #:machine-trace-fuel 8
                              #:machine-timeout 60
                              #:machine-sample-limit 12
                              #:verbose? #f))

(module+ main
  (run-theorem-random-checks!))
