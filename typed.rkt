#lang racket

;; language for typed abort/ctc model

(require redex/pict
         redex/reduction-semantics)

(provide typed-abort-lang
         typed-abort-red
         typed-abort-eval
         tc)

(define-language typed-abort-lang

  (e x v
     (binop e e) (unop e)
     (e e)
     (if e e e)
     (error string)
     (make-prompt-tag t t)
     (% e e (λ (x : t) e))
     (fix e)
     ;; annotate the abort in lieu of polymorphism/inference
     (abort t e e))

  (t num bool str (→ t t) (prompt t t))

  (v n b s (λ (x : t) e) p)

  (x variable-not-otherwise-mentioned)

  (n number)
  (b #t #f)
  (s string)
  (p (prompt-tag x t t))

  (binop + - *)
  (unop - not zero?)

  (E hole (binop E e) (binop v E) (unop E) (E e) (v E) (if E e e)
     (% e E v) (% E p v)
     (abort t E e) (abort t v E)))

(define typed-abort-red
  (reduction-relation typed-abort-lang
   #:domain e #:arrow ==>

   ;; primitives
   (--> (binop v_1 v_2) (delta_bin binop v_1 v_2) binop)
   (--> (unop v) (delta_un unop v) unop)

   ;; conditional
   (--> (if v e_1 e_2) e_1 (side-condition (term v)) if-true)
   (--> (if #f e_1 e_2) e_2 if-false)

   ;; lambda application
   (--> ((λ (x : t) e) v) (subst e x v) β)

   ;; error cases (application)
   (--> (v e)
        (error "application")
        (side-condition (not (term (procedure? v))))
        application-error)

   ;; prompt & prompt tags
   ;; E[(make-prompt-tag)]  |-->  E[x]  where x \not\in FV(E)
   (--> (make-prompt-tag t_1 t_2)
        (prompt-tag x_p t_1 t_2)
        (fresh x_p)
        prompt-tag)

   ;; no control effect
   (--> (% v p (λ (x : t) e)) v prompt)

   ;; normal abort without proxy
   (--> (% (in-hole E (abort t p v)) p v_h)
        (v_h v)
        (side-condition (term (no-match E p)))
        (side-condition (term (plain-prompt-tag? p)))
        abort/normal)

   ;; abort with a bad prompt tag value
   (--> (abort t v_1 v_2)
        (error "bad prompt tag")
        (side-condition (not (term (prompt-tag? v_1))))
        abort/error-bad-tag)

   ;; prompt with a bad prompt tag
   (--> (% e v v_h)
        (error "bad prompt tag")
        (side-condition (not (term (prompt-tag? v))))
        prompt/error-bad-tag)

   ;; abort without matching prompt tag
   (==> (in-hole E (abort t p v))
        (error "no matching prompt")
        (side-condition (term (no-match E p)))
        abort/error-missing-tag)

   ;; recursion
   (--> ((fix (λ (x : t) e)) v)
        (((λ (x : t) e) (fix (λ (x : t) e))) v)
        fix)

   ;; propagate error
   (==> (in-hole E (error string))
        (error string)
        (side-condition (not (equal? (term E) (term hole))))
        error)

   with
   [(==> (in-hole E a) (in-hole E b))
    (--> a b)]))

;; type checking
(define-extended-language abort+Γ typed-abort-lang
  (Γ · (x : t Γ)))

(define-judgment-form
  abort+Γ
  #:mode (tc I I O)
  #:contract (tc Γ e t)

  [(tc Γ e_1 (→ t_2 t_3))
   (tc Γ e_2 t_2)
   ---------------------- "TApp"
   (tc Γ (e_1 e_2) t_3)]

  [(tc (x : t_1 Γ) e t_2)
   ----------------------------------- "TLam"
   (tc Γ (λ (x : t_1) e) (→ t_1 t_2))]

  [(tc Γ e (→ (→ t_1 t_2) (→ t_1 t_2)))
   ------------------------------------ "TFix"
   (tc Γ (fix e) (→ t_1 t_2))]

  [-------------------
   (tc (x : t Γ) x t)]

  [(tc Γ x_1 t_1)
   (side-condition (different x_1 x_2))
   ------------------------------------
   (tc (x_2 : t_2 Γ) x_1 t_1)]

  [(tc Γ e_1 num) (tc Γ e_2 num)
   ----------------------------- "TPlus"
   (tc Γ (+ e_1 e_2) num)]

  [(tc Γ e_1 num) (tc Γ e_2 num)
   ----------------------------- "TMinus"
   (tc Γ (- e_1 e_2) num)]

  [(tc Γ e_1 num) (tc Γ e_2 num)
   ----------------------------- "TMult"
   (tc Γ (* e_1 e_2) num)]

  [(tc Γ e bool)
   ----------------- "TNot"
   (tc Γ (not e) bool)]

  [(tc Γ e num)
   ----------------- "TNeg"
   (tc Γ (- e) num)]

  [(tc Γ e num)
   ---------------------- "TZeroP"
   (tc Γ (zero? e) bool)]

  [-------------
   (tc Γ n num)]

  [---------------
   (tc Γ #t bool)]

  [---------------
   (tc Γ #f bool)]

  [---------------
   (tc Γ string str)]

  [(tc Γ e_1 bool)
   (tc Γ e_2 t)
   (tc Γ e_3 t)
   -------------------------- "TIf"
   (tc Γ (if e_1 e_2 e_3) t)]

  [-------------------------------------------------- "TMakePrompt"
   (tc Γ (make-prompt-tag t_1 t_2) (prompt t_1 t_2))]

  [------------------------------------------------- "TPromptTag"
   (tc Γ (prompt-tag x_p t_1 t_2) (prompt t_1 t_2))]

  [(tc Γ e_2 (prompt t_1 t_2))
   (tc Γ v (→ t_1 t_2)) (tc Γ e_1 t_2)
   ----------------------------------- "TPrompt"
   (tc Γ (% e_1 e_2 v) t_2)]

  [(tc Γ e_1 (prompt t_1 t_2)) (tc Γ e_2 t_1)
   ------------------------------------------ "TAbort"
   (tc Γ (abort t e_1 e_2) t)])

(define-metafunction abort+Γ
  [(different x_1 x_1) #f]
  [(different x_1 x_2) #t])

(module+ test
  (judgment-holds
   (tc · (+ 1 2) t)
   t)
  (judgment-holds
   (tc · ((λ (x : num) (+ x 5)) 3) t)
   t)
  (judgment-holds
   (tc · (if (zero? 0) "foo" "bar") t)
   t)
  (judgment-holds
   (tc · ((λ (pt : (prompt num num))
            (* (% (+ 1 (abort num pt 5))
                  pt
                  (λ (x : num) (+ x 5)))
               3))
          (make-prompt-tag num num))
       t)
   t))

(define-metafunction typed-abort-lang
  subst : any any e -> e
  ;; base cases
  [(subst n x e) n]
  [(subst b x e) b]
  [(subst s x e) s]
  ;; expressions
  [(subst (binop e_1 e_2) x e)
   (binop (subst e_1 x e) (subst e_2 x e))]
  [(subst (unop e_1) x e)
   (unop (subst e_1 x e))]
  [(subst (e_1 e_2) x e)
   ((subst e_1 x e) (subst e_2 x e))]
  [(subst (if e_1 e_2 e_3) x e)
   (if (subst e_1 x e) (subst e_2 x e) (subst e_3 x e))]
  [(subst (% e_1 e_2 e_3) x e)
   (% (subst e_1 x e) (subst e_2 x e) (subst e_3 x e))]
  [(subst (abort t e_1 e_2) x e)
   (abort t (subst e_1 x e) (subst e_2 x e))]
  [(subst (make-prompt-tag t_1 t_2) x e)
   (make-prompt-tag t_1 t_2)]
  [(subst (error string) x e) (error string)]
  [(subst (fix e_1) x e) (subst e_1 x e)]
  ;; variables
  [(subst x x e) e]
  [(subst x_1 x_2 e) x_1]
  ;; prompt tags (this has to be after var cases)
  [(subst p x e) p]
  ;; lambda
  [(subst (λ (x : t) e_b) x e)
   (λ (x : t) e_b)]
  [(subst (λ (x_1 : t) e_b) x_2 e)
   (λ (x_1 : t) (subst e_b x_2 e))])

;; MF: you do keep the rest of the language total. Cmp above with 'stuck'.
(define-metafunction typed-abort-lang
  delta_bin : binop v v -> e
  [(delta_bin + n_1 n_2)
   ,(+ (term n_1) (term n_2))]
  [(delta_bin - n_1 n_2)
   ,(- (term n_1) (term n_2))]
  [(delta_bin * n_1 n_2)
   ,(* (term n_1) (term n_2))]
  [(delta_bin binop v_1 v_2) (error "delta")])

(define-metafunction typed-abort-lang
  delta_un : unop v -> e
  [(delta_un - n_1)
   ,(- (term n_1))]
  [(delta_un not v_1)
   ,(not (term v_1))]
  [(delta_un zero? n_1)
   ,(zero? (term n_1))]
  [(delta_un number? v_1)
   ,(number? (term v_1))]
  [(delta_un string? v_1)
   ,(string? (term v_1))]
  [(delta_un boolean? v_1)
   ,(boolean? (term v_1))]
  [(delta_un procedure? (λ (x) e)) #t]
  [(delta_un procedure? (flat v)) #t]
  [(delta_un procedure? v) #f]
  [(delta_un prompt-tag? p) #t]
  [(delta_un prompt-tag? v) #f]
  [(delta_un unop v) (error "delta")])

;; used to make sure a given context is the closest one with the
;; matching prompt tag
(define-metafunction typed-abort-lang
  no-match : E p -> #t or #f
  [(no-match hole p) #t]
  [(no-match (% e E v) p) (no-match E p)]
  [(no-match (% E p_0 v) p_1)
   #f
   (side-condition (term (same-prompt-tag? p_0 p_1)))]
  [(no-match (% E p_0 v) p_1)
   (no-match E p_1)
   (side-condition (not (term (same-prompt-tag? p_0 p_1))))]
  [(no-match (binop E e) p) (no-match E p)]
  [(no-match (binop v E) p) (no-match E p)]
  [(no-match (unop E) p) (no-match E p)]
  [(no-match (E e) p) (no-match E p)]
  [(no-match (v E) p) (no-match E p)]
  [(no-match (if E e_1 e_2) p) (no-match E p)]
  [(no-match (abort t E e) p) (no-match E p)]
  [(no-match (abort t v E) p) (no-match E p)])

(define-metafunction typed-abort-lang
  same-prompt-tag? : p p -> #t or #f
  [(same-prompt-tag? (prompt-tag x t_1 t_2) (prompt-tag x t_3 t_4)) #t]
  [(same-prompt-tag? (prompt-tag x_1 t_1 t_2) (prompt-tag x_2 t_3 t_4)) #f])

(module+ test
  (test-equal
   (term (no-match (abort num #t hole) (prompt-tag x_p num num)))
   #t)
  (test-equal (term (no-match hole (prompt-tag x_p num num))) #t)
  (test-equal
   (term (no-match (% hole (prompt-tag x_p num num) (λ (x : num) (+ x 2)))
                   (prompt-tag x_p num num)))
   #f)
  (test-equal
   (term (no-match (% hole (prompt-tag x_p1 num num) (λ (x : num) (+ x 2)))
                   (prompt-tag x_p2 num num)))
   #t))

;; for application error cases
(define-metafunction typed-abort-lang
  procedure? : v -> #t or #f
  [(procedure? (λ (x : t) e)) #t]
  [(procedure? v) #f])

;; for error cases
(define-metafunction typed-abort-lang
  prompt-tag? : v -> #t or #f
  [(prompt-tag? (prompt-tag x_p t_1 t_2)) #t]
  [(prompt-tag? any) #f])

;; evaluator
;; term -> result
(define (typed-abort-eval t)
  (define results (apply-reduction-relation* typed-abort-red t))
  (define result (car results))
  (match result
    [(? number? n) n]
    [(? boolean? b) b]
    [(? string? s) s]
    [`(prompt-tag ,e ...) 'prompt-tag]
    [`(λ ,e ...) 'procedure]
    [`(error ,s) result]
    [else (error "Got stuck")]))

;; evaluation tests
(module+ test
  (require rackunit)
  (check-equal? (typed-abort-eval (term (+ 1 2)))
                3)
  (check-equal? (typed-abort-eval (term (λ (x : num) #t)))
                'procedure)
  (check-equal? (typed-abort-eval (term (make-prompt-tag num bool)))
                'prompt-tag))

;; helper for tests
(define-syntax-rule (tc-and-test lang t1 t2)
  (and (judgment-holds (tc · t1 t) t)
       (test-->> lang t1 t2)))

;; reduction relation tests
(module+ test
  ;; no control effect
  (tc-and-test
   typed-abort-red
   (term (% 5 (make-prompt-tag num num) (λ (x : num) x)))
   (term 5))

  ;; test basic abort & handle
  (tc-and-test
   typed-abort-red
   (term ((λ (pt : (prompt num num))
            (% (abort num pt 5)
               pt
               (λ (x : num) (+ x 1))))
          (make-prompt-tag num num)))
   (term 6))

  ;; abort past a prompt
  (tc-and-test
   typed-abort-red
   (term ((λ (pt : (prompt num num))
            (% (% (abort num pt 5)
                  (make-prompt-tag num num)
                  (λ (x : num) (+ x 2)))
               pt
               (λ (x : num) (+ x 1))))
          (make-prompt-tag num num)))
   (term 6))

  ;; abort to innermost prompt
  (tc-and-test
   typed-abort-red
   (term ((λ (pt : (prompt num num))
            (% (% (abort num pt 5)
                  pt
                  (λ (x : num) (+ x 2)))
               pt
               (λ (x : num) (+ x 1))))
          (make-prompt-tag num num)))
   (term 7))

  (tc-and-test
   typed-abort-red
   (term ((λ (pt : (prompt num num))
            (% (abort num pt 5)
               pt
               (λ (x : num) (+ x 1))))
          (make-prompt-tag num num)))
   (term 6)))

;; okay results for soundness
(define (okay-result? result)
  (match result
    [`(error ,s) (string=? s "no matching prompt")]
    [_ #t]))

(module+ main
  (redex-check abort+Γ e
               (implies (not (null? (judgment-holds (tc · e t) t)))
                        (okay-result? (typed-abort-eval (term e))))
               #:attempts 1000000))