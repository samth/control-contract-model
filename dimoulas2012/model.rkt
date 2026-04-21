#lang racket

;; Dimoulas et al. 2012 — "Complete Monitors for Behavioral Contracts" (ESOP 2012).
;; Standalone operational Redex model for the 2012 CM calculus.
;;
;; Paper / Lean correspondence:
;;   grammar (cm2012-lang)               <->  Dimoulas2012.Syntax (lambda/mu/ite/mon/check/own/ctcError)
;;   reduction `cm2012-red`              <->  Dimoulas2012.Syntax.Step (indy flavor)
;;   typing `cm2012-tc`                  <->  Dimoulas2012.Judgments.HasType
;;
;; The `dimoulas2012/blame.rkt` proof-layer is a separate presentation
;; of the 2012 well-formedness judgments over the full 2013 grammar.

(require redex/reduction-semantics
         rackunit)

(provide cm2012-lang
         cm2012-red
         cm2012-tc
         cm2012-eval/answer)

(define-language cm2012-lang
  (e x v
     (e e)
     (if e e e)
     (μ (x : t) e)
     (unop e)
     (monitor ctc e l l l)
     (check e v l l)
     (ctc-error l l)
     (own e l))

  (v b
     (λ (x : t) e)
     (own v l))

  (ctc (flat e)
       (flatAnnot e (l ...))
       (-> ctc ctc))

  (t B (→ t t) (Con t))
  (B Num Bool Unit)

  (x variable-not-otherwise-mentioned)
  ((l k j) string)

  (b n bool unit)
  (n integer)
  (bool #t #f)

  (unop - not zero? number? boolean? unit?)

  (E hole
     (E e)
     (v E)
     (if E e e)
     (unop E)
     (monitor ctc E l l l)
     (check E v l l)
     (own E l)))

(define cm2012-red
  (reduction-relation
   cm2012-lang
   #:domain e

   (--> (in-hole E ((λ (x : t) e) v))
        (in-hole E (subst e x v))
        beta/plain)

   (--> (in-hole E ((own (λ (x : t) e) l) v))
        (in-hole E (own (subst e x v) l))
        beta/own-fun)

   (--> (in-hole E ((own (λ (x : t) e) l) (own v l)))
        (in-hole E (own (subst e x (own v l)) l))
        beta/own)

   (--> (in-hole E (own (own e l) l))
        (in-hole E (own e l))
        own/collapse)

   ;; Paper-aligned: a bare `mu` (not yet wrapped in `own`) unfolds by
   ;; introducing an `own` with the ambient label, which at the top level
   ;; of the oracle and random-test harness is "τ". The legacy behavior
   ;; hard-coded the meta-label "μ"; the paper uses the ambient label
   ;; from the evaluation context, and the Lean `step?` does too.
   (--> (in-hole E (μ (x : t) e))
        (in-hole E (subst e x (own (μ (x : t) e) "τ")))
        mu/plain)

   (--> (in-hole E (own (μ (x : t) e) l))
        (in-hole E (own (subst e x (own (μ (x : t) e) l)) l))
        mu/own)

   (--> (in-hole E (if #t e_1 e_2)) (in-hole E e_1) if-true/plain)
   (--> (in-hole E (if #f e_1 e_2)) (in-hole E e_2) if-false/plain)
   (--> (in-hole E (if (own #t l) e_1 e_2)) (in-hole E e_1) if-true/own)
   (--> (in-hole E (if (own #f l) e_1 e_2)) (in-hole E e_2) if-false/own)

   (--> (in-hole E (unop v))
        (in-hole E (delta-un unop v))
        unop)

   (--> (in-hole E (monitor (flat e_pred) (own v k) k l j))
        (in-hole E (check (e_pred (strip-own (own v k))) (own v k) k j))
        flat/own)
   (--> (in-hole E (monitor (flatAnnot e_pred (l_1 ...)) (own v k) k l j))
        (in-hole E (check (e_pred (strip-own (own v k))) (own v k) k j))
        flatAnnot/own)
   (--> (in-hole E (monitor (flat e_pred) v k l j))
        (in-hole E (check (e_pred (strip-own v)) v k j))
        flat/plain)
   (--> (in-hole E (monitor (flatAnnot e_pred (l_1 ...)) v k l j))
        (in-hole E (check (e_pred (strip-own v)) v k j))
        flatAnnot/plain)

   ;; Arrow contract: paper's one-lambda form (Fig. 1)
   ;; mon(κ₁ ↦ κ₂, v) → λx. mon(κ₂, v mon(κ₁, x))
   (--> (in-hole E (monitor (-> ctc_a ctc_r) (λ (x : t) e) k l j))
        (in-hole E
                 (λ (arg : t)
                   (monitor ctc_r ((λ (x : t) e) (monitor ctc_a arg l k j)) k l j)))
        arrow/plain)

   (--> (in-hole E (monitor (-> ctc_a ctc_r) (own (λ (x : t) e) k) k l j))
        (in-hole E
                 (λ (arg : t)
                   (monitor ctc_r ((own (λ (x : t) e) k) (monitor ctc_a arg l k j)) k l j)))
        arrow/own)

   (--> (in-hole E (check #t v k j)) (in-hole E v) check-true/plain)
   (--> (in-hole E (check #f v k j)) (in-hole E (ctc-error k j)) check-false/plain)
   (--> (in-hole E (check (own #t j) v k j)) (in-hole E v) check-true/own)
   (--> (in-hole E (check (own #f j) v k j)) (in-hole E (ctc-error k j)) check-false/own)

   (--> (in-hole E (ctc-error k j))
        (ctc-error k j)
        (side-condition (not (equal? (term E) (term hole))))
        )))

(define-metafunction cm2012-lang
  delta-un : unop v -> e
  [(delta-un - n)
   ,(- (term n))]
  [(delta-un - (own v l))
   (own (strip-own (delta-un - (strip-own v))) l)]
  [(delta-un not #t) #f]
  [(delta-un not #f) #t]
  [(delta-un not (own v l))
   (own (strip-own (delta-un not (strip-own v))) l)]
  [(delta-un zero? n) ,(zero? (term n))]
  [(delta-un zero? (own v l))
   (own (strip-own (delta-un zero? (strip-own v))) l)]
  [(delta-un number? n) #t]
  [(delta-un number? (own v l))
   (own (strip-own (delta-un number? (strip-own v))) l)]
  [(delta-un number? v) #f]
  [(delta-un boolean? #t) #t]
  [(delta-un boolean? #f) #t]
  [(delta-un boolean? (own v l))
   (own (strip-own (delta-un boolean? (strip-own v))) l)]
  [(delta-un boolean? v) #f]
  [(delta-un unit? unit) #t]
  [(delta-un unit? (own v l))
   (own (strip-own (delta-un unit? (strip-own v))) l)]
  [(delta-un unit? v) #f])

(define-metafunction cm2012-lang
  subst : e x e -> e
  [(subst x x e_1) e_1]
  [(subst x_1 x_2 e_1) x_1]
  [(subst n x e) n]
  [(subst bool x e) bool]
  [(subst unit x e) unit]
  [(subst (e_1 e_2) x e_3)
   ((subst e_1 x e_3) (subst e_2 x e_3))]
  [(subst (if e_1 e_2 e_3) x e_4)
   (if (subst e_1 x e_4) (subst e_2 x e_4) (subst e_3 x e_4))]
  [(subst (μ (x : t) e) x e_1)
   (μ (x : t) e)]
  [(subst (μ (x_1 : t) e) x_2 e_1)
   (μ (x_1 : t) (subst e x_2 e_1))]
  [(subst (λ (x : t) e) x e_1)
   (λ (x : t) e)]
  [(subst (λ (x_1 : t) e) x_2 e_1)
   (λ (x_1 : t) (subst e x_2 e_1))]
  [(subst (unop e) x e_1)
   (unop (subst e x e_1))]
  [(subst (monitor ctc e k l j) x e_1)
   (monitor (subst-ctc ctc x e_1) (subst e x e_1) k l j)]
  [(subst (check e v k j) x e_1)
   (check (subst e x e_1) (subst v x e_1) k j)]
  [(subst (ctc-error k j) x e) (ctc-error k j)]
  [(subst (own e l) x e_1)
   (own (subst e x e_1) l)]
  [(subst ctc x e_1)
   (subst-ctc ctc x e_1)])

(define-metafunction cm2012-lang
  subst-ctc : ctc x e -> ctc
  [(subst-ctc (flat e) x e_1)
   (flat (subst e x e_1))]
  [(subst-ctc (flatAnnot e (l ...)) x e_1)
   (flatAnnot (subst e x e_1) (l ...))]
  [(subst-ctc (-> ctc_1 ctc_2) x e)
   (-> (subst-ctc ctc_1 x e) (subst-ctc ctc_2 x e))])

(define-metafunction cm2012-lang
  strip-own : e -> e
  [(strip-own (own e l))
   (strip-own e)]
  [(strip-own e) e])

(define-extended-language cm2012+Γ-lang cm2012-lang
  (Γ · (x : t Γ)))

(define-judgment-form
  cm2012+Γ-lang
  #:mode (cm2012-tc I I O)
  #:contract (cm2012-tc Γ any t)

  [(where t (lookup Γ x))
   ----------------------- TVar
   (cm2012-tc Γ x t)]

  [--------------------------- TInt
   (cm2012-tc Γ n Num)]

  [---------------------------- TTrue
   (cm2012-tc Γ #t Bool)]

  [----------------------------- TFalse
   (cm2012-tc Γ #f Bool)]

  [---------------------------- TUnit
   (cm2012-tc Γ unit Unit)]

  [(cm2012-tc (x : t_1 Γ) e t_2)
   ------------------------------------ TLam
   (cm2012-tc Γ (λ (x : t_1) e) (→ t_1 t_2))]

  [(cm2012-tc Γ e_1 (→ t_1 t_2))
   (cm2012-tc Γ e_2 t_1)
   ------------------------------- TApp
   (cm2012-tc Γ (e_1 e_2) t_2)]

  [(cm2012-tc Γ e_1 Bool)
   (cm2012-tc Γ e_2 t)
   (cm2012-tc Γ e_3 t)
   ------------------------------ TIf
   (cm2012-tc Γ (if e_1 e_2 e_3) t)]

  [(cm2012-tc (x : t Γ) e t)
   ------------------------------- TMu
   (cm2012-tc Γ (μ (x : t) e) t)]

  [(cm2012-tc Γ e Num)
   ------------------------- TNeg
   (cm2012-tc Γ (- e) Num)]

  [(cm2012-tc Γ e Bool)
   --------------------------- TNot
   (cm2012-tc Γ (not e) Bool)]

  [(cm2012-tc Γ e Num)
   ----------------------------- TZero
   (cm2012-tc Γ (zero? e) Bool)]

  [(cm2012-tc Γ e t)
   ------------------------------- TPredNum
   (cm2012-tc Γ (number? e) Bool)]

  [(cm2012-tc Γ e t)
   -------------------------------- TPredBool
   (cm2012-tc Γ (boolean? e) Bool)]

  [(cm2012-tc Γ e t)
   ------------------------------ TPredUnit
   (cm2012-tc Γ (unit? e) Bool)]

  [(cm2012-tc Γ e t)
   -------------------------- TOwn
   (cm2012-tc Γ (own e l) t)]

  [(cm2012-tc Γ e_pred (→ B Bool))
   ----------------------------------- TFlat
   (cm2012-tc Γ (flat e_pred) (Con B))]

  [(cm2012-tc Γ e_pred (→ B Bool))
   ---------------------------------------------- TFlatAnnot
   (cm2012-tc Γ (flatAnnot e_pred (l ...)) (Con B))]

  [(cm2012-tc Γ ctc_1 (Con t_1))
   (cm2012-tc Γ ctc_2 (Con t_2))
   ---------------------------------------------- TArrCtc
   (cm2012-tc Γ (-> ctc_1 ctc_2) (Con (→ t_1 t_2)))]

  [(cm2012-tc Γ ctc (Con t))
   (cm2012-tc Γ e t)
   ----------------------------------------------- TMonitor
   (cm2012-tc Γ (monitor ctc e k l j) t)]

  [(cm2012-tc Γ e Bool)
   (cm2012-tc Γ v t)
   ----------------------------------------------- TCheck
   (cm2012-tc Γ (check e v k j) t)])

(define-metafunction cm2012+Γ-lang
  lookup : Γ x -> t or #f
  [(lookup (x : t Γ) x) t]
  [(lookup (x_1 : t_1 Γ) x_2)
   (lookup Γ x_2)
   (side-condition (not (equal? (term x_1) (term x_2))))]
  [(lookup · x) #f])

(define (cm2012-eval/answer e #:fuel [fuel 200])
  (let loop ([current e] [remaining fuel])
    (define nexts (apply-reduction-relation cm2012-red current))
    (cond
      [(null? nexts)
       current]
      [(zero? remaining)
       'timeout]
      [else
       (loop (car nexts) (sub1 remaining))])))

(module+ test
  (check-equal?
   (cm2012-eval/answer
    '((λ (x : Num) x) 0))
   0)
  (check-equal?
   (cm2012-eval/answer
    '(if #t 0 1))
   0)
  (check-equal?
   (cm2012-eval/answer
    '((own (own (λ (x : Num) x) "τ") "τ") 0))
   '(own 0 "τ"))
  (check-equal?
   (cm2012-eval/answer
    '(check #f 0 "τ" "j"))
   '(ctc-error "τ" "j"))
  (check-equal?
   (judgment-holds
    (cm2012-tc · (ctc-error "τ" "j") t)
    t)
   '())
  (check-equal?
   (judgment-holds
    (cm2012-tc · (zero? #t) t)
    t)
   '())
  (check-not-false
   (member '(→ Num Num)
           (judgment-holds
            (cm2012-tc · (λ (x : Num) x) t)
            t)
           equal?)))
