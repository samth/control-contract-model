#lang racket

;; base language for abort/ctc model

(require redex/pict
         rackunit
         redex/reduction-semantics 
        (for-syntax syntax/parse))

(provide abort-core-lang
         abort-lang
         abort-red
         abort-eval
         tc
         let
         marks merge
         wrap+ wrap-
         no-match push)

(define-language abort-core-lang

  ;; programs
  (P (<> e σ))

  ;; store
  (σ · (key σ) (tag σ))

  ;; expressions
  (e x v (e e) (if e e e) (μ (x : t) e)
     (unop e) (binop e e) (cons e e)
     (case e (null = e) ((cons x x) = e))
     (make-prompt-tag t t) (make-cm-key t)
     (% e e v) (abort t e e) ; again with the type
     (wcm w e) (ccm e t)
     (call/comp e e) (call/cm e e e)
     (seq (update mk e) e) ; for doing wcm updates -- should track label
     (error))

  (v b (λ (x : t) e) pt mk
     (cons v v) (null t)
     call/comp call/cm)

  (w ((mk v) ...))

  (t B (→ t t) (Prompt t t)
     (Mark t) (List t))
  (B Num Bool Unit)

  (x variable-not-otherwise-mentioned)

  (b n s bool unit)
  (n number)
  (bool #t #f)

  ;; using variables for allocated tags/keys
  (pt tag)
  (mk key)
  (tag (variable-prefix tag))
  (key (variable-prefix key))

  (binop + - *)
  (unop - not zero? number? unit? boolean?)

  ;; still need this wcm non-adjacency here
  (E M (wcm w M))
  (M hole (if E e e) (E e) (v E)
     (unop E) (binop E e) (binop v E)
     (case E (null = e) ((cons x x) = e))
     (cons E e) (cons v E)
     (seq (update mk E) e)
     (% e E v) (% E pt v)
     (abort t E e) (abort t v E)
     (call/comp E e) (call/comp v E)
     (call/cm E e e) (call/cm v E e)))

;; define this in two stages for paper typesetting
(define-extended-language abort-lang abort-core-lang
  (e ....
     (monitor ctc e l l l)
     (ctc-error l l)
     (check e v l l))
  (pt ....
      (PG ctc ctc pt l l l))
  (mk ....
      (MG ctc mk l l l))
  (ctc (flat (λ (x : t) e))
       (-> ctc ctc)
       (prompt-tag/c ctc ctc t t)
       (mark/c ctc t)
       (list/c ctc))
  (t ....
     (Con t))
  ;; blame labels
  ((l k j) string)
  (M ....
     (monitor ctc E l l l)
     (check E v l l)))

(define abort-red
  (reduction-relation abort-lang
   #:domain P #:arrow ==>

   ;; primitives
   (--> (binop v_1 v_2) (delta_bin binop v_1 v_2) binop)
   (--> (unop v) (delta_un unop v) unop)

   ;; lists
   (--> (case (cons v_1 v_2)
          (null = e_1)
          ((cons x_1 x_2) = e_2))
        (subst (subst e_2 x_1 v_1) x_2 v_2)
        case/cons)
   (--> (case (null t)
          (null = e_1)
          ((cons x_1 x_2) = e_2))
        e_1
        case/null)

   ;; conditional
   (--> (if #t e_1 e_2) e_1 if-true)
   (--> (if #f e_1 e_2) e_2 if-false)

   ;; lambda application
   (--> ((λ (x : t) e) v)
        (subst e x v)
        β)

   ;; recursion
   (--> (μ (x : t) e)
        (subst e x (μ (x : t) e))
        μ)

   ;; call/comp
   (--> (% (in-hole E_pt (wcm w (call/comp v pt)))
           pt_1 v_h)
        (% (in-hole E_pt (wcm w (v (λ (x : t) e_k))))
           pt_1 v_h)
        (where/hidden (λ (x : t) e) v)
        (where e_k (wrap-c- pt (wrap-c+ pt_1 (in-hole E_pt x))))
        (side-condition/hidden (term (no-match E_pt pt)))
        (side-condition (term (same-prompt-tag? pt pt_1)))
        call/comp)

   ;; prompt & prompt tags
   ;; E[(make-prompt-tag)]  |-->  E[x]  where x \not\in FV(E)
   (==> (<> (in-hole E (make-prompt-tag t_1 t_2)) σ)
        (<> (in-hole E tag) (tag σ))
        (where/hidden tag ,(variable-not-in (term σ) 'tag))
        (side-condition (variable-not-in (term σ) 'tag))
        prompt-tag)

   ;; cont mark key
   (==> (<> (in-hole E (make-cm-key t)) σ)
        (<> (in-hole E key) (key σ))
        (where/hidden key ,(variable-not-in (term σ) 'key))
        (side-condition (variable-not-in (term σ) 'key))
        mark-key)

   ;; no control effect
   (--> (% v_1 pt v_2) v_1
        prompt)

   ;; abort (everything in one!)
   (--> (% (in-hole E_pt (abort t pt v)) pt_1 v_h)
        (v_h (in-hole E_+ (in-hole E_- v)))
        (where E_+ (wrap+ pt_1))
        (where E_- (wrap- pt hole))
        (side-condition/hidden (term (no-match E_pt pt)))
        (side-condition (term (same-prompt-tag? pt pt_1)))
        abort)

   ;; flat contracts
   ;; MF: your flat syntax allows only a value i.e. (flat v)
   ;; which is good !!!
   ;; and this suggests that you meant 'monitor' not 'contract' here
   ;; 
   ;; Rule #14 (had to remove names for typesetting)
   (--> (monitor (flat v_f) v k l j)
        (check (v_f v) v k j))

   (--> (check #t v l j) v)
   (--> (check #f v l j) (ctc-error l j))

   ;; ->
   (--> (monitor (-> ctc_a ctc_r) (name v (λ (x : t) e)) k l j)
        (λ (x_1 : t)
           ((λ (x_2 : t) (monitor ctc_r (v x_2) k l j))
            (monitor ctc_a x_1 l k j))))

   ;; prompt-tag/c
   (--> (monitor (prompt-tag/c ctc_1 ctc_2 t_1 t_2) v_p k l j)
        (PG ctc_1 ctc_2 v_p k l j))

   ;; mark/c
   (--> (monitor (mark/c ctc t) v_m k l j)
        (MG ctc v_m k l j))

   ;; list/c
   (--> (monitor (list/c ctc) (null t) k l j)
        (null t))
   (--> (monitor (list/c ctc) (cons v_1 v_2) k l j)
        (cons (monitor ctc v_1 k l j) (monitor (list/c ctc) v_2 k l j)))

   ;; just a value
   (--> (wcm w v) v wcm/v)

   ;; wcm merging
   (--> (wcm w_1 (wcm w_2 e))
        (wcm (merge w_1 w_2) e)
        wcm/merge)

   ;; get a mark
   (==> (<> (in-hole E (ccm key t)) σ)
        (<> (in-hole E (marks E key (null t))) σ)
        ccm)

   ;; get mark values with a guarded key
   (--> (ccm (MG ctc mk k l j) t)
        (monitor (list/c ctc) (ccm mk t) k l j)
        ccm/guard)

   ;; turn a call/cm into an update
   (--> (wcm w (call/cm mk v e))
        (wcm w (seq (update mk_1 e_1) e))
        (where (mk_1 e_1) (push mk v))
        call/cm)

   ;; special mark update
   (--> (wcm ((key_1 v_1) ...
              (key_2 v_2) (key_3 v_3) ...)
             (seq (update key_2 v_4) e))
        (wcm ((key_1 v_1) ...
              (key_2 v_4) (key_3 v_3) ...)
             e)
        wcm/set)

   ;; add a mark
   (--> (wcm ((key_1 v_1) ...)
             (seq (update key_2 v_2) e))
        (wcm ((key_1 v_1) ... (key_2 v_2)) e)
        (side-condition (term (not-in key_2 (key_1 ...)))) 
        wcm/add)

   ;; introduce mark environment
   (==> (<> (in-hole E (call/cm v_1 v_2 e)) σ)
        (<> (in-hole E (wcm () (call/cm v_1 v_2 e))) σ)
        (side-condition (term (not-wcm E)))
        wcm/intro/cm)

   (==> (<> (in-hole E (call/comp v_1 v_2)) σ)
        (<> (in-hole E (wcm () (call/comp v_1 v_2))) σ)
        (side-condition (term (not-wcm E)))
        wcm/intro/comp)

   ;; propagate error
   (==> (<> (in-hole E (ctc-error l j)) σ)
        (<> (ctc-error l j) σ)
        (side-condition/hidden (not (equal? (term E) (term hole))))
        ctc-error)

   (==> (<> (in-hole E (error)) σ)
        (<> (error) σ)
        (side-condition (not (equal? (term E) (term hole)))))

   with
   [(==> (<> (in-hole E a) σ) (<> (in-hole E aa) σ))
    (--> a aa)]))

;; wrapping contracts
(define-metafunction abort-lang
  wrap+ : pt -> E
  [(wrap+ (PG ctc_1 ctc_2 pt k l j))
   (monitor ctc_1 (wrap+ pt) k l j)]
  [(wrap+ tag) hole])

(define-metafunction abort-lang
  wrap- : pt E -> E
  [(wrap- (PG ctc_1 ctc_2 pt k l j) E)
   (wrap- pt (monitor ctc_1 E l k j))]
  [(wrap- tag E) E])

(define-metafunction abort-lang
  wrap-c+ : pt e -> e
  [(wrap-c+ (PG ctc_1 ctc_2 pt k l j) e)
   (monitor ctc_2 (wrap-c+ pt e) l k j) ]
  [(wrap-c+ tag e) e])

(define-metafunction abort-lang
  wrap-c- : pt e -> e
  [(wrap-c- (PG ctc_1 ctc_2 pt k l j) e)
   (wrap-c- pt (monitor ctc_2 e k l j))]
  [(wrap-c- tag e) e])

;; extract true prompt tag out
(define-metafunction abort-lang
  extract : pt -> pt
  [(extract (PG ctc_1 ctc_2 pt k l j)) (extract pt)]
  [(extract tag) tag])

;; push value into mark guards
(define-metafunction abort-lang
  push : mk e -> (mk e)
  [(push (MG ctc mk k l j) e)
   (push mk (monitor ctc e l k j))]
  [(push key e) (key e)])

;; check if this mark key is in the current w
;; cheats a bit via Racket
(define-metafunction abort-lang
  not-in : v (v ...) -> #t or #f
  [(not-in mk_2 (mk_1 ...))
   ,(not (member (term mk_2) (term (mk_1 ...))))])

;; check that wcm doesn't wrap the hole
(define-metafunction abort-lang
  not-wcm : E -> #t or #f
  [(not-wcm (in-hole E (wcm w hole))) #f]
  [(not-wcm E) #t])

(module+ test
  (check-false (term (not-wcm (wcm () hole))))
  (check-false (term (not-wcm (+ 5 (wcm () hole)))))
  (check-true (term (not-wcm hole)))
  (check-true (term (not-wcm (abort Num hole 5)))))

;; wcm merging, second takes precedence
(define-metafunction abort-lang
  merge : w w -> w
  [(merge () w) w]
  [(merge ((v_1 v_2) (v_3 v_4) ...)
          ((v_5 v_6) ... (v_1 v_7) (v_8 v_9) ...))
   (merge ((v_3 v_4) ...)
          ((v_5 v_6) ... (v_1 v_7) (v_8 v_9) ...))]
  [(merge ((v_1 v_2) (v_3 v_4) ...)
          ((v_5 v_6) ...))
   (merge ((v_3 v_4) ...)
          ((v_5 v_6) ... (v_1 v_2)))])

;; just for convenience
(define-metafunction abort-lang
  [(let ([(x : any_t) any_e1]) any_e2) ((λ (x : any_t) any_e2) any_e1)])

;; type checking
(define-extended-language abort+Γ-lang abort-lang
  (Γ · (x : t Γ))
  (Σ · (v : t Σ)))

(define-judgment-form
  abort+Γ-lang
  #:mode (tc I I I O)
  #:contract (tc Γ Σ any t)

  [(tc Γ Σ e_1 (→ t_2 t_3))
   (tc Γ Σ e_2 t_2)
   ------------------------ TApp
   (tc Γ Σ (e_1 e_2) t_3)]

  [(tc (x : t_1 Γ) Σ e t_2)
   ------------------------------------ TLam
   (tc Γ Σ (λ (x : t_1) e) (→ t_1 t_2))]

  [(tc (x : t Γ) Σ e t)
   ------------------------ TMu
   (tc Γ Σ (μ (x : t) e) t)]

  [(tc Γ Σ e_1 (List t_1))
   (tc Γ Σ e_2 t_2)
   (tc (x_2 : (List t_1) (x_1 : t_1 Γ)) Σ e_3 t_2)
   ----------------------------------------------------------- TCase
   (tc Γ Σ (case e_1 (null = e_2) ((cons x_1 x_2) = e_3)) t_2)]

  [-------------------------- TNull
   (tc Γ Σ (null t) (List t))]

  [(tc Γ Σ v_1 t)
   (tc Γ Σ v_2 (List t))
   -------------------------------- TCons
   (tc Γ Σ (cons v_1 v_2) (List t))]

  [(where t (∈ x Γ))
   ----------------- TVar
   (tc Γ Σ x t)]

  [(tc Γ Σ e_1 t_1) (tc Γ Σ e_2 t_2)
   (where (t_1 t_2 t_3) (Δt-bin binop))
   ------------------------------------ TBinOp
   (tc Γ Σ (binop e_1 e_2) t_3)]

  [(tc Γ Σ e t_1)
   (where (t_1 t_2) (Δt-un unop t_1))
   ---------------------------------- TUnOp
   (tc Γ Σ (unop e) t_2)]

  [-------------- TNum
   (tc Γ Σ n Num)]

  [---------------- TTrue
   (tc Γ Σ #t Bool)]

  [---------------- TFalse
   (tc Γ Σ #f Bool)]

  [------------------ TUnit
   (tc Γ Σ unit Unit)]

  [(tc Γ Σ e_1 Bool)
   (tc Γ Σ e_2 t)
   (tc Γ Σ e_3 t)
   --------------------------- TIf
   (tc Γ Σ (if e_1 e_2 e_3) t)]

  ;; Control
  [--------------------------------------------------- TMakePrompt
   (tc Γ Σ (make-prompt-tag t_1 t_2) (Prompt t_1 t_2))]

  [(where (Prompt t_1 t_2) (∈ tag Σ))
   ---------------------------------- TPromptTag
   (tc Γ Σ tag (Prompt t_1 t_2))]

  [(tc Γ Σ v (Prompt t_1 t_2))
   (tc Γ Σ ctc_1 (Con (Prompt t_1 t_2)))
   -------------------------------------------------- TPromptGuard
   (tc Γ Σ (PG ctc_1 ctc_2 v k l j) (Prompt t_1 t_2))]

  [(tc Γ Σ e_1 t_2)
   (tc Γ Σ v (→ t_1 t_2))
   (tc Γ Σ e_2 (Prompt t_1 t_2))
   ----------------------------- TPrompt
   (tc Γ Σ (% e_1 e_2 v) t_2)]

  [(tc Γ Σ e_2 t_1)
   (tc Γ Σ e_1 (Prompt t_1 t_2))
   ----------------------------- TAbort
   (tc Γ Σ (abort t e_1 e_2) t)]

  [(tc Γ Σ e_1 (→ (→ t_3 t_2) t_3))
   (tc Γ Σ e_2 (Prompt t_1 t_2))
   -------------------------------- TCallComp
   (tc Γ Σ (call/comp e_1 e_2) t_3)]

  ;; Marks
  [(tc Γ Σ e_1 (Mark t_1))
   (tc Γ Σ e_2 t_1) (tc Γ Σ e_3 t_2)
   ---------------------------------- TCallCM
   (tc Γ Σ (call/cm e_1 e_2 e_3) t_2)]

  [(tc Γ Σ e t)
   (tc Γ Σ mk (Mark t_1)) ...
   (tc Γ Σ v t_1) ...
   --------------------------------------------- TWCM
   (tc Γ Σ (wcm ((mk v) ...) e) t)]

  [(tc Γ Σ e (Mark t))
   --------------------------- TCCM
   (tc Γ Σ (ccm e t) (List t))]

  [--------------------------------- TMakeKey
   (tc Γ Σ (make-cm-key t) (Mark t))]

  [(where (Mark t) (∈ key Σ))
   -------------------------- TKey
   (tc Γ Σ key (Mark t))]

  [(tc Γ Σ ctc (Con (Mark t)))
   (tc Γ Σ v (Mark t))
   ---------------------------------- TKeyGuard
   (tc Γ Σ (MG ctc v k l j) (Mark t))]

  ;; Contracts
  [(tc Γ Σ e (→ B Bool))
   ------------------------- TConFlat
   (tc Γ Σ (flat e) (Con B))]

  [(tc Γ Σ ctc_1 (Con t_1)) (tc Γ Σ ctc_2 (Con t_2))
   ------------------------------------------------- TConFun
   (tc Γ Σ (-> ctc_1 ctc_2) (Con (→ t_1 t_2)))]

  [(tc Γ Σ ctc_1 (Con t_1)) (tc Γ Σ ctc_2 (Con t_2))
   ------------------------------------------------------------------ TConPrompt
   (tc Γ Σ (prompt-tag/c ctc_1 ctc_2 t_1 t_2) (Con (Prompt t_1 t_2)))]

  [(tc Γ Σ ctc (Con t))
   -------------------------------------- TConMark
   (tc Γ Σ (mark/c ctc t) (Con (Mark t)))]

  [(tc Γ Σ ctc (Con t))
   ------------------------------------ TConList
   (tc Γ Σ (list/c ctc) (Con (List t)))]

  [(tc Γ Σ ctc (Con t)) (tc Γ Σ e t)
   --------------------------------- TMon
   (tc Γ Σ (monitor ctc e k l j) t)])

(define-metafunction abort+Γ-lang
  [(Δt-bin +) (Num Num Num)]
  [(Δt-bin -) (Num Num Num)]
  [(Δt-bin *) (Num Num Num)])

(define-metafunction abort+Γ-lang
  [(Δt-un - t) (Num Num)]
  [(Δt-un not t) (Bool Bool)]
  [(Δt-un zero? t) (Num Bool)]
  [(Δt-un number? t) (t Bool)]
  [(Δt-un unit? t) (t Bool)]
  [(Δt-un boolean? t) (t Bool)])

(define-metafunction abort+Γ-lang
  ∈ : any any -> t or #f
  [(∈ x (x : t Γ)) t]
  [(∈ x_2 (x_1 : t_1 Γ))
   (∈ x_2 Γ)
   (side-condition (term (different x_1 x_2)))]
  [(∈ x (v : t Σ)) t]
  [(∈ v_2 (v_1 : t_1 Σ))
   (∈ v_2 Σ)
   (side-condition (term (different v_1 v_2)))]
  [(∈ any ·) #f])

(define-metafunction abort+Γ-lang
  [(different any_1 any_1) #f]
  [(different any_1 any_2) #t])

(module+ test
  (judgment-holds
   (tc · · (+ 1 2) t)
   t)
  (judgment-holds
   (tc · · ((λ (x : Num) (+ x 5)) 3) t)
   t)
  (judgment-holds
   (tc · · (if (zero? 0) #t #f) t)
   t)
  (judgment-holds
   (tc · ·
       ((λ (pt : (Prompt Num Num))
           (* (% (+ 1 (abort Num pt 5))
                 pt
                 (λ (x : Num) (+ x 5)))
              3))
        (make-prompt-tag Num Num))
       t)
   t)
  (judgment-holds
   (tc · · (flat (λ (x : Num) (zero? x))) t)
   t)
  (judgment-holds
   (tc ·
       (tag0 : (Prompt Num Num) ·)
       (monitor (prompt-tag/c
                 (flat (λ (x : Num) (zero? x)))
                 (flat (λ (x : Num) (zero? x)))
                 Num Num)
         tag0
         "pos"
         "neg"
         "con")
       t)
   t))

;; encoding for the paper
(define-metafunction abort-lang
  [(call/cc (name v (λ (x_1 : (→ t_1 t_2)) e_1)) e)
   (call/comp
    (λ (kont : (→ t_1 t_2))
      (v (λ (x : t_1)
           (abort t_2 e (λ (y : Unit) (kont x))))))
    e)])

(define-metafunction abort-lang
  subst-n : e (x ...) (e ...) -> e
  [(subst-n e () ()) e]
  [(subst-n e (x_1 x_2 ...) (e_1 e_2 ...))
   (subst-n (subst e x_1 e_1) (x_2 ...) (e_2 ...))])

(define-metafunction abort-lang
  subst : e x e -> e
  ;; base cases
  [(subst n x e) n]
  [(subst b x e) b]
  [(subst s x e) s]
  [(subst unit x e) unit]
  [(subst call/comp x e) call/comp]
  [(subst call/cm x e) call/cm]
  [(subst binop x e) binop]
  [(subst unop x e) unop]
  ;; expressions
  [(subst (binop e_1 e_2) x e_3)
   (binop (subst e_1 x e_3) (subst e_2 x e_3))]
  [(subst (unop e) x e_1)
   (unop (subst e x e_1))]
  [(subst (e_1 e_2 ...) x e_3)
   ((subst e_1 x e_3) (subst e_2 x e_3) ...)]
  [(subst (if e_1 e_2 e_3) x e_4)
   (if (subst e_1 x e_4) (subst e_2 x e_4) (subst e_3 x e_4))]
  ;; this might be simplifiable
  [(subst (case e_1 (null = e_2) ((cons x x_2) = e_3)) x e_4)
   (case (subst e_1 x e_4)
     (null = (subst e_2 x e_4))
     ((cons x x_2) = e_3))]
  [(subst (case e_1 (null = e_2) ((cons x_1 x) = e_3)) x e_4)
   (case (subst e_1 x e_4)
     (null = (subst e_2 x e_4))
     ((cons x_1 x) = e_3))]
  [(subst (case e_1 (null = e_2) ((cons x_1 x_2) = e_3)) x e_4)
   (case (subst e_1 x e_4)
     (null = (subst e_2 x e_4))
     ((cons x_1 x_2) = (subst e_3 x e_4)))]
  [(subst (cons e_1 e_2) x e)
   (cons (subst e_1 x e) (subst e_2 x e))]
  [(subst (% e_1 e_2 e_3) x e_4)
   (% (subst e_1 x e_4) (subst e_2 x e_4) (subst e_3 x e_4))]
  [(subst (abort t e_1 e_2) x e_4)
   (abort t (subst e_1 x e_4) (subst e_2 x e_4))]
  [(subst (make-prompt-tag t_1 t_2) x e)
   (make-prompt-tag t_1 t_2)]
  [(subst (call/comp v_1 e_1) x e_2)
   (call/comp (subst v_1 x e_2) (subst e_1 x e_2))]
  [(subst (ccm e t) x e_1) (ccm (subst e x e_1) t)]
  [(subst (wcm w e) x e_1) (wcm w (subst e x e_1))]
  [(subst (error) x e) (error)]
  [(subst (ctc-error l j) x e) (ctc-error l j)]
  ;; variables
  [(subst x x e) e]
  [(subst x_1 x_2 e) x_1]
  ;; prompt tags (this has to be after var cases)
  [(subst (PG ctc_1 ctc_2 pt k l j) x e)
   (PG (subst-ctc ctc_1 x e)
       (subst-ctc ctc_2 x e)
       (subst pt x e) k l j)]
  [(subst tag x e) tag]
  ;; mark keys
  [(subst (MG ctc mk k l j) x e)
   (MG (subst-ctc ctc x e) (subst mk x e) k l j)]
  [(subst key x e) key]
  ;; lambda
  [(subst (λ (x : t) e) x e_1)
   (λ (x : t) e)]
  [(subst (λ (x_1 : t_1) e) x_2 e_1)
   (λ (x_1 : t_1) (subst e x_2 e_1))]
  ;; mu
  [(subst (μ (x : t) e) x e_1)
   (μ (x : t) e)]
  [(subst (μ (x_1 : t_1) e) x_2 e_1)
   (μ (x_1 : t_1) (subst e x_2 e_1))]
  ;; contracts
  [(subst (monitor ctc e k l j) x e_1)
   (monitor (subst-ctc ctc x e_1) (subst e x e_1) k l j)]
  [(subst ctc x e_1)
   (subst-ctc ctc x e_1)])

(define-metafunction abort-lang
  subst-ctc : ctc x e -> ctc
  [(subst-ctc (flat e) x e_1)
   (flat (subst e x e_1))]
  [(subst-ctc (-> ctc_a ctc_r) x e)
   (-> (subst-ctc ctc_a x e) (subst-ctc ctc_r x e))]
  [(subst-ctc (prompt-tag/c ctc_1 ctc_2 t_1 t_2) x e)
   (prompt-tag/c (subst-ctc ctc_1 x e)
                 (subst-ctc ctc_2 x e)
                 t_1 t_2)]
  [(subst-ctc (mark/c ctc t) x e)
   (mark/c (subst-ctc ctc x e) t)]
  [(subst-ctc (list/c ctc) x e)
   (list/c (subst-ctc ctc x e))])

;; MF: you do keep the rest of the language total. Cmp above with 'stuck'.
(define-metafunction abort-lang
  delta_bin : binop v v -> e
  [(delta_bin + n_1 n_2)
   ,(+ (term n_1) (term n_2))]
  [(delta_bin - n_1 n_2)
   ,(- (term n_1) (term n_2))]
  [(delta_bin * n_1 n_2)
   ,(* (term n_1) (term n_2))]
  [(delta_bin binop v_1 v_2) (error)])

(define-metafunction abort-lang
  delta_un : unop v -> e
  [(delta_un - n_1)
   ,(- (term n_1))]
  [(delta_un not v_1)
   ,(not (term v_1))]
  [(delta_un zero? n_1)
   ,(zero? (term n_1))]
  [(delta_un number? v_1)
   ,(number? (term v_1))]
  [(delta_un boolean? v_1)
   ,(boolean? (term v_1))]
  [(delta_un unit? v_1)
   ,(eq? 'unit (term v_1))]
  [(delta_un procedure? (λ ([x : t] ...) e)) #t]
  [(delta_un procedure? (flat v)) #t]
  [(delta_un procedure? v) #f]
  [(delta_un prompt-tag? pt) #t]
  [(delta_un prompt-tag? v) #f]
  [(delta_un unop v) (error)])

;; used to make sure a given context is the closest one with the
;; matching prompt tag
(define-metafunction abort-lang
  no-match : E pt -> #t or #f
  [(no-match hole pt) #t]
  [(no-match (% e E v) pt) (no-match E pt)]
  [(no-match (% E pt_0 v) pt_1)
   #f
   (side-condition (term (same-prompt-tag? pt_0 pt_1)))]
  [(no-match (% E pt_0 v) pt_1)
   (no-match E pt_1)
   (side-condition (not (term (same-prompt-tag? pt_0 pt_1))))]
  [(no-match (binop E e) pt) (no-match E pt)]
  [(no-match (binop v E) pt) (no-match E pt)]
  [(no-match (unop E) pt) (no-match E pt)]
  [(no-match (E e) pt) (no-match E pt)]
  [(no-match (v E) pt) (no-match E pt)]
  [(no-match (if E e_1 e_2) pt) (no-match E pt)]
  [(no-match (case E (null = e_1) ((cons x_1 x_2) = e_2)) pt)
   (no-match E pt)]
  [(no-match (abort t E e) pt) (no-match E pt)]
  [(no-match (abort t v E) pt) (no-match E pt)]
  [(no-match (wcm w E) pt) (no-match E pt)]
  [(no-match (monitor ctc E k l j) pt) (no-match E pt)])

(define-metafunction abort-lang
  same-prompt-tag? : pt pt -> #t or #f
  [(same-prompt-tag? pt pt) #t]
  [(same-prompt-tag? (PG ctc_1 ctc_2 pt_1 k l j) pt_2)
   (same-prompt-tag? pt_1 pt_2)]
  [(same-prompt-tag? pt_1 (PG ctc_1 ctc_2 pt_2 k l j))
   (same-prompt-tag? pt_1 pt_2)]
  [(same-prompt-tag? tag_1 tag_2) #f])

(module+ test
  (test-equal
   (term (no-match (wcm ((key_0 0)) hole) tag_0))
   #t)
  (test-equal
   (term (no-match (wcm () hole) tag_0))
   #t)
  (test-equal
   (term (no-match (abort Bool #t hole) tag_0))
   #t)
  (test-equal (term (no-match hole tag_0)) #t)
  (test-equal
   (term (no-match (% hole
                      tag_0 
                      (λ (x : Num) (+ x 2)))
                   tag_0))
   #f)
  (test-equal
   (term (no-match (% hole
                      tag_0
                      (λ (x : Num) (+ x 2)))
                   tag_1))
   #t))

;; for continuation marks
(define-metafunction abort-lang
  marks : E v v -> v
  [(marks hole v v_1) v_1]
  [(marks (wcm w_1 E_1) v_3 v)
   (marks E_1 v_3 (cons v_4 v))
   (where ((v_1 v_2) ... (v_3 v_4) (v_5 v_6) ...) w_1)]
  [(marks (wcm w E) v v_1)
   (marks E v v_1)
   ;; re-write this more Redex-y later
   (side-condition/hidden (not (member (term v) (map car (term w)))))]
  [(marks (E e_1) v v_1) (marks E v v_1)]
  [(marks (v_1 E) v_2 v_3) (marks E v_2 v_3)]
  [(marks (binop E e) v_2 v_1) (marks E v_2 v_1)]
  [(marks (binop v E) v_2 v_1) (marks E v_2 v_1)]
  [(marks (unop E) v_2 v_1) (marks E v_2 v_1)]
  [(marks (if E e e) v_2 v_1) (marks E v_2 v_1)]
  [(marks (case E (null = e_1) ((cons x_1 x_2) = e_2)) v_2 v_1)
   (marks E v_2 v_1)]
  [(marks (% e E v) v_2 v_1) (marks E v_2 v_1)]
  [(marks (% E pt v) v_2 v_1) (marks E v_2 v_1)]
  [(marks (monitor ctc E k l j) v_2 v_1) (marks E v_2 v_1)]
  [(marks (abort t E e) v_2 v_1) (marks E v_2 v_1)]
  [(marks (abort t v E) v_2 v_1) (marks E v_2 v_1)]
  [(marks (call/comp v E) v_2 v_1) (marks E v_2 v_1)]
  [(marks (call/cm E v_3 e) v_2 v_1) (marks E v_2 v_1)])

;; evaluator
;; term [store] -> result
(define (abort-eval t #:init-store [store (term ·)])
  (define state (term (<> ,t ,store)))
  (define results (apply-reduction-relation* abort-red state))
  (define result (cadr (car results)))
  (match result
    [(? number? n) n]
    [(? boolean? b) b]
    [`(cons ,v_1 ,v_2) `(cons ,v_1 ,v_2)]
    ['key 'mark-key]
    [`(MG ,e ...) 'mark-key]
    ['tag 'prompt-tag]
    [`(PG ,e ...) 'prompt-tag]
    [`(λ ,e ...) 'procedure]
    [`(-> ,e_1 ,e_2) 'contract]
    [`(prompt-tag/c ,e ...) 'contract]
    [`(mark/c ,e ...) 'contract]
    ;; flat contracts are 'procedure even though they could be
    ;; 'contract (this works better since all unary procedures are
    ;;  contracts in Racket)
    [`(flat ,e) 'procedure]
    [`(ctc-error ,e_1 ,e_2) `(ctc-error ,e_1 ,e_2)]
    [`(error) 'error]
    [else (error (format "Got stuck: ~a" result))]))

;; evaluation tests
(module+ test
  (require rackunit)
  (check-equal? (abort-eval (term (+ 1 2)))
                3)
  (check-equal? (abort-eval (term (λ (x : Num) #t)))
                'procedure)
  (check-equal? (abort-eval (term (make-prompt-tag Num Bool)))
                'prompt-tag))

;; helper for tests
(define-syntax (do-test stx)
  (syntax-parse stx
    [(_ ?input ?expected)
     #'(do-test ?input ?expected
                #:init-store (term ·)
                #:store-type ·)]
    [(_ ?input ?expected #:init-store ?store #:store-type ?store-type)
     #'(begin
        (check-true (judgment-holds (tc · ?store-type ,?input t)))
        (check-equal? (abort-eval ?input #:init-store ?store)
                      ?expected))]))

;; eval and type checking tests
(module+ test
  ;; recursion
  (do-test
   (term ((μ (f : (→ Num Num))
             (λ (n : Num)
               (if (zero? n)
                   1
                   (* n (f (- n 1))))))
          5))
   (term 120))

  ;; list recursion
  (do-test
   (term ((μ (f : (→ (List Num) Num))
             (λ (lst : (List Num))
               (case lst
                 (null = 0)
                 ((cons x1 x2) =
                  (+ x1 (f x2))))))
          (cons 5 (cons 6 (null Num)))))
   (term 11))

  ;; list contract
  (do-test
   (term (monitor (list/c (flat (λ (x : Num) (zero? x))))
                  (cons 0 (cons 6 (null Num)))
                  "pos" "neg" "con"))
   (term (ctc-error "pos" "con")))

  ;; no control effect
  (do-test
   (term (% 5 (make-prompt-tag Num Num) (λ (x : Num) x)))
   (term 5))

  ;; test basic abort & handle
  (do-test
   (term (let ([(pt : (Prompt Num Num))
                (make-prompt-tag Num Num)])
           (% (abort Num pt 5)
              pt
              (λ (x : Num) (+ x 1)))))
   (term 6))

  ;; abort past a prompt
  (do-test
   (term (let ([(pt : (Prompt Num Num))
                (make-prompt-tag Num Num)])
           (% (% (abort Num pt 5)
                 (make-prompt-tag Num Num)
                 (λ (x : Num) (+ x 2)))
              pt
              (λ (x : Num) (+ x 1)))))
   (term 6))

  ;; abort to innermost prompt
  (do-test
   (term (let ([(pt : (Prompt Num Num))
                (make-prompt-tag Num Num)])
           (% (% (abort Num pt 5)
                 pt
                 (λ (x : Num) (+ x 2)))
              pt
              (λ (x : Num) (+ x 1)))))
   (term 7))

  ;; composable continuations
  (do-test
   (term (let ([(pt : (Prompt Num Num))
                (make-prompt-tag Num Num)])
           (% (+ 1 (call/comp
                     (λ (kont : (→ Num Num))
                       (+ (kont 3) (kont 5)))
                     pt))
              pt
              (λ (x : Num) x))))
   (term 11))

  (do-test
   (term (let ([(pt : (Prompt (→ Unit Num) Num))
                (make-prompt-tag (→ Unit Num) Num)])
           (% (+ 1 (call/comp
                    (λ (kont : (→ Num Num))
                      (abort Num pt
                             (λ (x : Unit)
                               (+ (kont 3) (kont 5)))))
                    pt))
              pt
              (λ (kont : (→ Unit Num)) (kont unit)))))
   (term 10))

  ;; call/cc encoding
  (do-test
   (term (let ([(pt : (Prompt (→ Unit Num) Num))
                (make-prompt-tag (→ Unit Num) Num)])
           (% (+ 1 (call/cc
                     (λ (kont : (→ Num Num))
                       (+ (kont 3) (kont 5)))
                     pt))
              pt
              (λ (kont : (→ Unit Num)) (kont unit)))))
   (term 4))

  ;; handler destroys call/cc semantics
  (do-test
   (term (let ([(pt : (Prompt (→ Unit Num) Num))
                (make-prompt-tag (→ Unit Num) Num)])
           (% (+ 1 (call/cc
                     (λ (kont : (→ Num Num))
                       (+ (kont 3) (kont 5)))
                     pt))
              pt
              (λ (kont : (→ Unit Num)) 18))))
   (term 18))

  ;; continuation marks
  (do-test
   (term (let ([(mk : (Mark Num))
                (make-cm-key Num)])
           (call/cm
            mk 5
            (ccm mk Num))))
   (term (cons 5 (null Num))))

  (do-test
   (term (let ([(mk : (Mark Num))
                (make-cm-key Num)])
           (call/cm
            mk 5
            (call/cm
             mk 7
             (ccm mk Num)))))
   (term (cons 7 (null Num))))

  ;; make sure wcms merge in weird cases
  (do-test
   (term ((λ (f : (→ Unit (List Num)))
             (wcm ((key0 5)) (f unit)))
          (λ (x : Unit)
             (wcm ((key0 3)) (ccm key0 Num)))))
   (term (cons 3 (null Num)))
   #:init-store (term (key0 ·))
   #:store-type (key0 : (Mark Num) ·))

  ;; continuation mark contracts
  (do-test
   (term (let ([(mk : (Mark Num))
                (monitor (mark/c (flat (λ (x : Num) (zero? x))) Num)
                         (make-cm-key Num)
                         "pos"
                         "neg"
                         "con")])
           (call/cm
            mk 5
            (ccm mk Num))))
   (term (ctc-error "neg" "con")))

  (do-test
   (term (let ([(mk : (Mark Num))
                (monitor (mark/c (flat (λ (x : Num) (zero? x))) Num)
                         (make-cm-key Num)
                         "pos"
                         "neg"
                         "con")])
           (call/cm
            mk 0
            (ccm mk Num))))
   (term (cons 0 (null Num))))

  ;; naive contract
  (do-test
   (term (let ([(pt : (Prompt Num Num))
                (make-prompt-tag Num Num)])
           (% (monitor (flat (λ (x : Num) (number? x)))
                       (abort Num pt 5)
                       "pos"
                       "neg"
                       "con")
              pt
              (λ (x : Num) (+ x 1)))))
   (term 6))

  ;; first-order checks
  (do-test
   (term (monitor (flat (λ (x : Num) (zero? x)))
                  5
                  "server"
                  "client"
                  "con"))
   (term (ctc-error "server" "con")))

  ;; prompt & abort in the same component, the tag elsewhere
  (do-test
   (term (let ([(pt : (Prompt Num Num))
                (monitor (prompt-tag/c (flat (λ (x : Num) (zero? x)))
                                       (flat (λ (x : Num) (zero? x)))
                                       Num Num)
                         (make-prompt-tag Num Num)
                         "server"
                         "client"
                         "con")])
           (% (abort Num pt 3)
              pt
              (λ (x : Num) (+ x 1)))))
   (term (ctc-error "client" "con")))

  ;; call/comp issue
  (do-test
   (term (let ([(pt : (Prompt Num Num))
                (monitor (prompt-tag/c (flat (λ (x : Num) (zero? x)))
                                       (flat (λ (x : Num) (zero? x)))
                                       Num Num)
                         (make-prompt-tag Num Num)
                         "server"
                         "client"
                         "con")])
           (% (+ 1
                 (call/comp
                  (λ (k : (→ Num Num))
                    (k 0))
                  pt))
              pt
              (λ (x : Num) (+ x 1)))))
   (term (ctc-error "client" "con")))

  ;; blame even on one side
  (do-test
   (term (let ([(pt1 : (Prompt Num Num))
                (make-prompt-tag Num Num)])
           (let ([(pt2 : (Prompt Num Num))
                  (monitor (prompt-tag/c (flat (λ (x : Num) (zero? x)))
                                         (flat (λ (x : Num) (zero? (- x 5))))
                                         Num Num)
                           pt1
                           "client"
                           "server"
                           "con")])
             (% (+ 1 ; doesn't add to 5
                   (call/comp
                    (λ (k : (→ Num Num))
                      (k 3))
                    pt1))
                pt2
                (λ (x : Num) (+ x 1))))))
   (term (ctc-error "server" "con")))

  ;; blame even on other side
  (do-test
   (term (let ([(pt1 : (Prompt Num Num))
                (make-prompt-tag Num Num)])
           (let ([(pt2 : (Prompt Num Num))
                  (monitor (prompt-tag/c (flat (λ (x : Num) (zero? x)))
                                         (flat (λ (x : Num) (zero? (- x 5))))
                                         Num Num)
                           pt1
                           "server"
                           "client"
                           "con")])
             (% (+ 1 ; doesn't add to 5
                   (call/comp
                    (λ (k : (→ Num Num))
                      (k 3))
                    pt2))
                pt1
                (λ (x : Num) (+ x 1))))))
   (term (ctc-error "server" "con")))

  ;; same with ho-contract
  (do-test
   (term (let ([(pt : (Prompt (→ Num Num) Num))
                (monitor (prompt-tag/c (-> (flat (λ (x : Num) (zero? x)))
                                           (flat (λ (x : Num) (number? x))))
                                       (flat (λ (x : Num) (number? x)))
                                       (→ Num Num) Num)
                         (make-prompt-tag (→ Num Num) Num)
                         "server"
                         "client"
                         "con")])
           (% (abort Num pt (λ (x : Num) 5))
              pt
              (λ (x : (→ Num Num)) (x 8)))))
   (term (ctc-error "client" "con")))

  ;; again, but from other side
  (do-test
   (term (let ([(pt : (Prompt (→ Num Num) Num))
                (monitor (prompt-tag/c (-> (flat (λ (x : Num) (zero? x)))
                                           (flat (λ (x : Num) (zero? x))))
                                       (flat (λ (x : Num) (zero? x)))
                                       (→ Num Num) Num)
                         (make-prompt-tag (→ Num Num) Num)
                         "server"
                         "client"
                         "con")])
           (% (abort Num pt (λ (x : Num) 3))
              pt
              (λ (f : (→ Num Num)) (f 0)))))
   (term (ctc-error "client" "con")))

  ;; abort across boundary w/ ho-value
  (do-test
   (term (let ([(do-prompt : (→ (→ (Prompt (→ Num Num) Num) Num) Num))
                (let ([(pt : (Prompt (→ Num Num) Num))
                       (make-prompt-tag (→ Num Num) Num)])
                  (monitor (-> (-> (prompt-tag/c (-> (flat (λ (x : Num) (zero? x)))
                                                     (flat (λ (x : Num) (zero? x))))
                                                 (flat (λ (x : Num) (zero? x)))
                                                 (→ Num Num) Num)
                                   (flat (λ (x : Num) (number? x))))
                               (flat (λ (x : Num) (number? x))))
                           (λ (f : (→ (Prompt (→ Num Num) Num) Num))
                              (% (f pt)
                                 pt
                                 (λ (f : (→ Num Num)) (f 5))))
                           "server"
                           "client"
                           "con"))])
           (do-prompt
            (λ (pt : (Prompt (→ Num Num) Num))
              (abort Num pt (λ (v : Num) (+ v 1)))))))
   (term (ctc-error "server" "con"))) ;; MF: nice example but in a paper presentation you need to simplify

  ;; where the prompt flows across multiple boundaries
  (do-test
   (term (let ([(do-prompt : (→ (→ (Prompt (→ Num Num) Num) Num) Num))
                (let ([(pt : (Prompt (→ Num Num) Num))
                       (make-prompt-tag (→ Num Num) Num)])
                  (monitor (-> (-> (prompt-tag/c (-> (flat (λ (x : Num) (number? x)))
                                                     (flat (λ (x : Num) (number? x))))
                                                 (flat (λ (x : Num) (number? x)))
                                                 (→ Num Num) Num)
                                   (flat (λ (x : Num) (number? x))))
                               (flat (λ (x : Num) (number? x))))
                           (λ (f : (→ (Prompt (→ Num Num) Num) Num))
                             (% (f pt)
                                pt
                                (λ (f : (→ Num Num)) (f 1))))
                           "A"
                           "B"
                           "con1"))])
           (let ([(do-prompt-2 : (→ (→ (Prompt (→ Num Num) Num) Num) Num))
                  (monitor (-> (-> (prompt-tag/c (-> (flat (λ (x : Num) (zero? x)))
                                                     (flat (λ (x : Num) (number? x))))
                                                 (flat (λ (x : Num) (number? x)))
                                                 (→ Num Num) Num)
                                   (flat (λ (x : Num) (number? x))))
                               (flat (λ (x : Num) (number? x))))
                           (λ (f : (→ (Prompt (→ Num Num) Num) Num))
                             (do-prompt f))
                           "B"
                           "C"
                           "con2")])
             (do-prompt-2
              (λ (pt : (Prompt (→ Num Num) Num))
                (abort Num pt (λ (v : Num) (+ v 1))))))))
   (term (ctc-error "B" "con2")))

  #|
  ;; from random test generation
  (do-test
   (term (boolean?
          (abort (monitor
                  (prompt-tag/c (-> (flat (λ (H) (error)))
                                    (flat (λ (R) (error)))))
                  (prompt-tag v)
                  "pos"
                  "neg")
                 (make-prompt-tag))))
   (term (error)))
   |#
   )
