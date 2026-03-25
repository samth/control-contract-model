#lang racket

(require redex/reduction-semantics
         "model.rkt")

(provide blame-lang blame-red
         wfsp wfctc wfctci wfip lwfp wfst
         wfmp wtmp ctc->type ctcwitnessp)

;; language for blame completeness
;; only for type-setting since this is very hard to compute with
(define-extended-language blame-lang abort-lang
  (e ....
     (own e l)
     (seq (update l mk e) e))
  (v ....
     (own v l))
  (ctc ....
       (oblig (flat e) (l ...)))

  (E ....
     (own E l)
     (own-final F l))
  (F M (wcm w M))
  (M hole
     (if E e e)
     (case E (null e) ((cons x x) e))
     (seq (update l mk E) e)
     (v ... E e ...)
     (% e E v) (% E p v)
     (abort t E e) (abort t v E)))

(define-extended-language blame+Γ-lang blame-lang
  (S · (x : l Γ)) ; only typesetting
  (G · (x : l Γ)) ;
  (Γ · (x : l Γ))
  (Σ · (v : l Γ)))

;; complete monitor reduction
;; this reduction relation has no computational content
(define blame-red
  (reduction-relation blame-lang
   #:domain P #:arrow ==>

   ;; primitives (junk, not typeset)
   (--> (binop v_1 v_2) v_1 binop)
   (--> (unop v) v unop)

   ;; lists
   (--> (case (single-own (cons v_1 v_2) l)
          (null e_1)
          ((cons x_1 x_2) e_2))
        (subst (subst e_2 x_1 v_1) x_2 v_2)
        case/cons)
   (--> (case (single-own (null t) l)
          (null e_1)
          ((cons x_1 x_2) e_2))
        e_1
        case/null)

   ;; conditional
   (--> (if (single-own #t l) e_1 e_2) e_1 if-true)
   (--> (if (single-own #f l) e_1 e_2) e_2 if-false)

   ;; lambda application
   (--> ((single-own (λ (x : t) e) l) (single-own v l))
        (own (subst e x (own v l)) l)
        β)

   ;; recursion
   (--> (μ (x : t) e)
        (subst e x (own (μ (x : t) e) l))
        μ)

   ;; call/comp
   (--> (% (in-hole E_pt^k (wcm w (call/comp (single-own v k) (single-own pt k))))
           (single-own pt_1 l) (single-own v_h l))
        (% (in-hole E_pt^k (wcm w ((own v k) (own (cont E) k))))
           (single-own pt_1 l) (single-own v_h l))
        (side-condition/hidden (term (no-match E_^k (single-own pt k))))
        (side-condition (term (same-prompt-tag? pt pt_1)))
        call/comp)

   ;; prompt & prompt tags
   ;; E[(make-prompt-tag)]  |-->  E[x]  where x \not\in FV(E)
   (==> (<> (in-hole E_^l (make-prompt-tag t_1 t_2)) σ)
        (<> (in-hole E_^l tag) (tag σ))
        (where/hidden tag ,(variable-not-in (term σ) 'tag))
        (side-condition (variable-not-in (term σ) 'tag))
        prompt-tag)

   ;; cont mark key
   (==> (<> (in-hole E_^l (make-cm-key t)) σ)
        (<> (in-hole E_^l key) (key σ))
        (where/hidden key ,(variable-not-in (term σ) 'key))
        (side-condition (variable-not-in (term σ) 'key))
        mark-key)

   ;; no control effect
   (--> (% (single-own v_1 l) (single-own pt l) (single-own v_2 l))
        v_1
        prompt)

   ;; abort (everything in one!)
   (--> (% (in-hole E_^k (abort t (single-own pt k) (single-own v k))) (single-own pt_1 l) (single-own v_h l))
        ((own v_h l) (in-hole E_+^j (in-hole E_-^k (own v k))))
        (where E_+^j (wrap+ pt_1))
        (where E_-^k (wrap- pt hole))
        (side-condition/hidden (term (no-match E_pt (extract pt))))
        (side-condition (term (same-prompt-tag? pt pt_1)))
        abort)

   ;; flat contracts
   ;; ESOP 2012 allows arbitrary predicate code in flat contracts; the contract
   ;; system applies it to the witness value when monitoring fires.
   (--> (monitor (oblig (flat e_f) (l_1. ...)) (single-own v l_1) k l j)
        (check (e_f v) v k j))

   (--> (check (single-own #t j) v l j) v)
   (--> (check (single-own #f j) v l j) (ctc-error l j))

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
   (--> (wcm w (single-own v l)) v wcm/v)

   ;; wcm merging
   (--> (wcm w_1 (wcm w_2 e))
        (wcm (merge w_1 w_2) e)
        wcm/merge)

   ;; get a mark
   (==> (<> (in-hole E_^l (ccm (single-own key l) t)) σ)
        (<> (in-hole E_^l (marks E key (null t))) σ)
        ccm)

   ;; get mark values with a guarded key
   (--> (ccm (MG ctc (single-own mk k) k l j) t)
        (monitor ctc (ccm (own mk k) t) k l j)
        ccm/guard)

   ;; turn a call/cm into an update
   (--> (wcm w (call/cm (single-own mk l) (single-own v l) e))
        (wcm w (seq (update k key e_1) e))
        (where (key e_1 k) (push mk v))
        call/cm)

   ;; special mark update
   (--> (wcm ((key_1 v_1) ... (key_2 v_2) (key_3 v_3) ...)
             (seq (update k key_2 (single-own v_4 k)) e))
        (wcm ((key_1 v_1) ... (key_2 v_4) (key_3 v_3) ...)
             e)
        wcm/set)

   ;; add a mark
   (--> (wcm ((key_1 v_1) ...)
             (seq (update k key_2 (single-own v_2 k)) e))
        (wcm ((key_1 v_1) ... (key_2 v_2)) e)
        (side-condition/hidden (term (not-in key_2 (key_1 ...))))
        wcm/add)

   ;; introduce mark environment
   (==> (<> (in-hole E_^l (call/cm (single-own v_1 l) (single-own v_2 l) e)) σ)
        (<> (in-hole E_^l (wcm () (call/cm (own v_1 l) (own v_2 l) e))) σ)
        (side-condition (term (not-wcm E)))
        wcm/intro/cm)

   (==> (<> (in-hole E_^l (call/comp (single-own v_1 l) (single-own v_2 l))) σ)
        (<> (in-hole E_^l (wcm () (call/comp (own v_1 l) (own v_2 l)))) σ)
        (side-condition (term (not-wcm E)))
        wcm/intro/comp)

   ;; propagate error
   (:--> (in-hole E_^l (ctc-error k j))
         (ctc-error k j)
         (side-condition/hidden (not (equal? (term E) (term hole))))
         ctc-error)

   (:--> (in-hole E (error))
        (error)
        (side-condition (not (equal? (term E) (term hole)))))

   with
   [(==> (<> a σ) (<> aa σ))
    (:--> a aa)]
   [(==> (<> (in-hole E a) σ) (<> (in-hole E aa) σ))
    (--> a aa)]))

;; well-formed source programs
(define-judgment-form
  blame+Γ-lang
  #:mode (wfsp I I I I)
  #:contract (wfsp Σ Γ l e)

  [(wfsp Σ Γ l e_1)
   (wfsp Σ Γ l e_2)
   ---------------------- WApp
   (wfsp Σ Γ l (e_1 e_2))]

  [(wfsp Σ (x : l Γ) l e)
   ---------------------------- WLam
   (wfsp Σ Γ l (λ (x : t_1) e))]

  [(wfsp Σ (x : l Γ) l e)
   -------------------------- WMu
   (wfsp Σ Γ l (μ (x : t) e))]

  [(wfsp Σ Γ l e_1)
   (wfsp Σ Γ l e_2)
   (wfsp Σ (x_2 : l (x_1 : l Γ)) l e_3)
   ------------------------------------------------------- WCase
   (wfsp Σ Γ l (case e_1 (null = e_2) ((cons x_1 x_2) = e_3)))]

  [--------------------- WNull
   (wfsp Σ Γ l (null t))]

  [(wfsp Σ Γ l e_1)
   (wfsp Σ Γ l e_2)
   --------------------------- WCons
   (wfsp Σ Γ l (cons e_1 e_2))]

  [(where l (∈ Γ x))
   ----------------- WVar
   (wfsp Σ Γ l x)]

  [(wfsp Σ Γ l e_1) (wfsp Σ Γ l e_2)
   --------------------------------- WBinOp
   (wfsp Σ Γ l (binop e_1 e_2))]

  [(wfsp Σ Γ l e)
   --------------------- WUnOp
   (wfsp Σ Γ l (unop e))]

  [-------------- WNum
   (wfsp Σ Γ l n)]

  [--------------- WTrue
   (wfsp Σ Γ l #t)]

  [---------------- WFalse
   (wfsp Σ Γ l #f)]

  [--------------- WUnit
   (wfsp Σ Γ l unit)]

  [(wfsp Σ Γ l e_1)
   (wfsp Σ Γ l e_2) (wfsp Σ Γ l e_3)
   ----------------------------- WIf
   (wfsp Σ Γ l (if e_1 e_2 e_3))]

  [(wfsp Σ Γ l e)
   ---------------------- WOwn
   (wfsp Σ Γ l (own e l))]

  ;; Control
  [-------------------------------------- WMakePrompt
   (wfsp Σ Γ l (make-prompt-tag t_1 t_2))]

  [(where l (∈ Σ tag))
   ------------------- WPromptTag
   (wfsp Σ Γ l tag)]
  
  [(wfsp Σ Γ k v)
   (wfctc Σ Γ (k l) (k l) j ctc_1)
   (wfctc Σ Γ (k l) (k l) j ctc_2)
   -------------------------------------------- WPromptGuard
   (wfsp Σ Γ l (PG ctc_1 ctc_2 v k l j))]

  [(wfsp Σ Γ l e_1)
   (wfsp Σ Γ l e_2) (wfsp Σ Γ l v)
   ------------------------------- WPrompt
   (wfsp Σ Γ l (% e_1 e_2 v))]

  [(wfsp Σ Γ l e_1)
   (wfsp Σ Γ l e_2)
   ------------------------------ WAbort
   (wfsp Σ Γ l (abort t e_1 e_2))]

  [(wfsp Σ Γ l e_1)
   (wfsp Σ Γ l e_2)
   -------------------------------- WCallComp
   (wfsp Σ Γ l (call/comp e_1 e_2))]

  ;; Marks
  [(wfsp Σ Γ l e_1)
   (wfsp Σ Γ l e_2) (wfsp Σ Γ l e_3)
   ---------------------------------- WCallCM
   (wfsp Σ Γ l (call/cm e_1 e_2 e_3))]

  [(wfsp Σ Γ l e)
   (wfsp Σ Γ l key) ...
   (wfsp Σ Γ l v) ...
   ----------------------------------------- WWCM
   (wfsp Σ Γ l (wcm ((key v) ...) e))]

  [(wfsp Σ Γ k key)
   (wfsp Σ Γ k v) (wfsp Σ Γ l e)
   ---------------------------------------------- WUpdate
   (wfsp Σ Γ l (seq (update k key v) e))]

  [(wfsp Σ Γ l e)
   ---------------------- WCCM
   (wfsp Σ Γ l (ccm e t))]

  [---------------------------- WMakeKey
   (wfsp Σ Γ l (make-cm-key t))]

  [(where l (∈ Σ key))
   ------------------- WKey
   (wfsp Σ Γ l key)]

  [(wfsp Σ Γ k v) (wfctc Σ Γ (k l) (k l) j ctc)
   -------------------------------------------- WKeyGuard
   (wfsp Σ Γ l (MG ctc v k l j))]
  
  [(wfsp Σ Γ k e)
   (wfctc Σ Γ (k) (l) j ctc)
   ------------------------------------------ WMon
   (wfsp Σ Γ l (monitor ctc (own e k) k l j))])

;; Source contract well-formedness
(define-judgment-form
  blame+Γ-lang
  #:mode (wfctc I I I I I I)

  [(wfsp Σ Γ j e)
   -------------------------------------------------------------- WCFlat
   (wfctc Σ Γ (k ...) (l ...) j (oblig (flat (own e j)) (k ...)))]

  [(wfctc Σ Γ (l ...) (k ...) j ctc_1)
   (wfctc Σ Γ (k ...) (l ...) j ctc_2)
   ---------------------------------------------- WCFun
   (wfctc Σ Γ (k ...) (l ...) j (-> ctc_1 ctc_2))]

  [(wfctc Σ Γ (k ...) (l ...) j ctc_1)
   (wfctc Σ Γ (k ...) (l ...) j ctc_2)
   -------------------------------------------------------- WCPrompt
   (wfctc Σ Γ (k ...) (l ...) j (prompt-tag/c ctc_1 ctc_2 t_1 t_2))]

  [(wfctc Σ Γ (k ...) (l ...) j ctc)
   -------------------------------------------- WCMark
   (wfctc Σ Γ (k ...) (l ...) j (mark/c ctc t)) ]
  
  [(wfctc Σ Γ (k ...) (l ...) j ctc)
   -------------------------------------------- WCList
   (wfctc Σ Γ (k ...) (l ...) j (list/c ctc))])

;; Intermediate contract well-formedness: positive obligations need only be a subset
;; of the annotated obligation list on flat contracts.
(define-metafunction blame+Γ-lang
  label-member : l (l ...) -> boolean
  [(label-member l ()) #f]
  [(label-member l (l l_rest ...)) #t]
  [(label-member l_1 (l_2 l_rest ...))
   (label-member l_1 (l_rest ...))
   (side-condition (term (different l_1 l_2)))])

(define-metafunction blame+Γ-lang
  labels-subset : (l ...) (l ...) -> boolean
  [(labels-subset () (l_2 ...)) #t]
  [(labels-subset (l_1 l_rest ...) (l_2 ...))
   #t
   (where #t (label-member l_1 (l_2 ...)))
   (where #t (labels-subset (l_rest ...) (l_2 ...)))]
  [(labels-subset (l_1 l_rest ...) (l_2 ...))
   #f])

(define-judgment-form
  blame+Γ-lang
  #:mode (wfctci I I I I I I)

  [(wfsp Σ Γ j e)
   (where #t (labels-subset (k ...) (k_oblig ...)))
   ----------------------------------------------------------------- WCFlatI
   (wfctci Σ Γ (k ...) (l ...) j (oblig (flat (own e j)) (k_oblig ...)))]

  [(wfctci Σ Γ (l ...) (k ...) j ctc_1)
   (wfctci Σ Γ (k ...) (l ...) j ctc_2)
   ----------------------------------------------- WCFunI
   (wfctci Σ Γ (k ...) (l ...) j (-> ctc_1 ctc_2))]

  [(wfctci Σ Γ (k ...) (l ...) j ctc_1)
   (wfctci Σ Γ (k ...) (l ...) j ctc_2)
   --------------------------------------------------------- WCPromptI
   (wfctci Σ Γ (k ...) (l ...) j (prompt-tag/c ctc_1 ctc_2 t_1 t_2))]

  [(wfctci Σ Γ (k ...) (l ...) j ctc)
   --------------------------------------------- WCMarkI
   (wfctci Σ Γ (k ...) (l ...) j (mark/c ctc t))]

  [(wfctci Σ Γ (k ...) (l ...) j ctc)
   --------------------------------------------- WCListI
   (wfctci Σ Γ (k ...) (l ...) j (list/c ctc))])

;; Paper-style loose well-formedness / repair states (ESOP 2012 Fig. 6)
(define-judgment-form
  blame+Γ-lang
  #:mode (lwfp I I I I)

  [(where l (∈ Γ x))
   ----------------- LWVar
   (lwfp Σ Γ l x)]
  
  [(wfsp Σ Γ l e_1)
   (wfsp Σ Γ l e_2)
   ------------------------------ LWApp
   (lwfp Σ Γ l ((own e_1 l) e_2))]

  [(wfsp Σ Γ l e)
   --------------------------- LWCCM
   (lwfp Σ Γ l (ccm (own e l) t))]

  [(lwfp Σ Γ l e)
   ---------------------------------- LWMon
   (lwfp Σ Γ l (monitor ctc e k l j))])

;; Generalized intermediate terms. This is the larger subject used for progress and
;; preservation; `lwfp` above is only the bounded repair judgment.
(define-judgment-form
  blame+Γ-lang
  #:mode (wfip I I I I)

  [(wfsp Σ Γ l e)
   --------------------- WISource
   (wfip Σ Γ l e)]

  [(lwfp Σ Γ l e)
   -------------------- WILoose
   (wfip Σ Γ l e)]

  [(wfip Σ Γ l e_1)
   (wfip Σ Γ l e_2)
   ---------------------- WIApp
   (wfip Σ Γ l (e_1 e_2))]

  [(wfip Σ (x : l Γ) l e)
   ---------------------------- WILam
   (wfip Σ Γ l (λ (x : t_1) e))]

  [(wfip Σ (x : l Γ) l e)
   -------------------------- WIMu
   (wfip Σ Γ l (μ (x : t) e))]

  [(wfip Σ Γ l e_1)
   (wfip Σ Γ l e_2)
   (wfip Σ (x_2 : l (x_1 : l Γ)) l e_3)
   ------------------------------------------------------- WICase
   (wfip Σ Γ l (case e_1 (null = e_2) ((cons x_1 x_2) = e_3)))]

  [--------------------- WINull
   (wfip Σ Γ l (null t))]

  [(wfip Σ Γ l e_1)
   (wfip Σ Γ l e_2)
   --------------------------- WICons
   (wfip Σ Γ l (cons e_1 e_2))]

  [(where l (∈ Γ x))
   ----------------- WIVar
   (wfip Σ Γ l x)]

  [(wfip Σ Γ l e_1) (wfip Σ Γ l e_2)
   --------------------------------- WIBinOp
   (wfip Σ Γ l (binop e_1 e_2))]

  [(wfip Σ Γ l e)
   --------------------- WIUnOp
   (wfip Σ Γ l (unop e))]

  [-------------- WINum
   (wfip Σ Γ l n)]

  [--------------- WITrue
   (wfip Σ Γ l #t)]

  [---------------- WIFalse
   (wfip Σ Γ l #f)]

  [--------------- WIUnit
   (wfip Σ Γ l unit)]

  [-------------------------- WICtcError
   (wfip Σ Γ l (ctc-error k j))]

  [(wfip Σ Γ l e_1)
   (wfip Σ Γ l e_2) (wfip Σ Γ l e_3)
   ----------------------------- WIIf
   (wfip Σ Γ l (if e_1 e_2 e_3))]

  [(wfip Σ Γ l e)
   ---------------------- WIOwn
   (wfip Σ Γ l (own e l))]

  [-------------------------------------- WIMakePrompt
   (wfip Σ Γ l (make-prompt-tag t_1 t_2))]

  [(where l (∈ Σ tag))
   ------------------- WIPromptTag
   (wfip Σ Γ l tag)]

  [(wfip Σ Γ k v)
   (wfctci Σ Γ (k l) (k l) j ctc_1)
   (wfctci Σ Γ (k l) (k l) j ctc_2)
   -------------------------------------------- WIPromptGuard
   (wfip Σ Γ l (PG ctc_1 ctc_2 v k l j))]

  [(wfip Σ Γ l e_1)
   (wfip Σ Γ l e_2) (wfip Σ Γ l v)
   ------------------------------- WIPrompt
   (wfip Σ Γ l (% e_1 e_2 v))]

  [(wfip Σ Γ l e_1)
   (wfip Σ Γ l e_2)
   ------------------------------ WIAbort
   (wfip Σ Γ l (abort t e_1 e_2))]

  [(wfip Σ Γ l e_1)
   (wfip Σ Γ l e_2)
   -------------------------------- WICallComp
   (wfip Σ Γ l (call/comp e_1 e_2))]

  [(wfip Σ Γ l e_1)
   (wfip Σ Γ l e_2) (wfip Σ Γ l e_3)
   ---------------------------------- WICallCM
   (wfip Σ Γ l (call/cm e_1 e_2 e_3))]

  [(wfip Σ Γ l e)
   (wfip Σ Γ l key) ...
   (wfip Σ Γ l v) ...
   ----------------------------------------- WIWCM
   (wfip Σ Γ l (wcm ((key v) ...) e))]

  [(wfip Σ Γ k key)
   (wfip Σ Γ k v) (wfip Σ Γ l e)
   ---------------------------------------------- WIUpdate
   (wfip Σ Γ l (seq (update k key v) e))]

  [(wfip Σ Γ l e)
   ---------------------- WICCM
   (wfip Σ Γ l (ccm e t))]

  [---------------------------- WIMakeKey
   (wfip Σ Γ l (make-cm-key t))]

  [(where l (∈ Σ key))
   ------------------- WIKey
   (wfip Σ Γ l key)]

  [(wfip Σ Γ k v) (wfctci Σ Γ (k l) (k l) j ctc)
   -------------------------------------------- WIKeyGuard
   (wfip Σ Γ l (MG ctc v k l j))]

  [(wfip Σ Γ k e)
   (wfctci Σ Γ (k) (l) j ctc)
   ------------------------------------------ WIMon
   (wfip Σ Γ l (monitor ctc e k l j))]

  [(lwfp Σ Γ j e)
   (wfip Σ Γ l v)
   ------------------------------------------ WICheck
   (wfip Σ Γ l (check e v k j))])

;; Well formed store
(define-judgment-form
  blame+Γ-lang
  #:mode (wfst I I)

  [----------
   (wfst Σ ·)]

  [(where l (∈ Σ key))
   (wfst Σ σ)
   ------------------------
   (wfst Σ (key σ))]

  [(where l (∈ Σ tag))
   (wfst Σ σ)
   ------------------------
   (wfst Σ (tag σ))])

;; Stronger contract-error witness, matching the ESOP 2012 complete-monitoring
;; definition more closely than mere reachability of `(ctc-error k j)`.
(define-judgment-form
  blame+Γ-lang
  #:mode (ctcwitnessp I I I)

  [(where #t (label-member k (k_oblig ...)))
   -------------------------------------------------------------- CTCWitness
   (ctcwitnessp (in-hole E_^l (monitor (oblig (flat e_f) (k_oblig ...))
                                      (own v k) k l j))
                k j)])

;; Well-formed mixed program
(define-judgment-form
  blame+Γ-lang
  #:mode (wfmp I I I)
 
  [(wtmp Σ Γ e (ctc->type ctc))
   (wfctc Σ Γ (t) (u) j ctc)
   --------------------------------
   (wfmp Σ Γ (monitor ctc e t u j))])

;; Well-typed mixed program
(define-judgment-form
  blame+Γ-lang
  #:mode (wtmp I I I I)

  [(wfmp Σ Γ e)
   (wfctc Σ Γ (t) (u) j ctc)
   ------------------------------------------------
   (wtmp Σ Γ (monitor ctc e t u j) (ctc->type ctc))])

;; contract <-> type metafunction
(define-metafunction
  blame+Γ-lang
  [(ctc->type (oblig (flat (own (λ (x : t) e) j)) (l ...)))
   t]
  [(ctc->type (oblig (flat (λ (x : t) e)) (l ...)))
   t]
  [(ctc->type (flat (own (λ (x : t) e) j)))
   t]
  [(ctc->type (flat (λ (x : t) e)))
   t]
  [(ctc->type (-> ctc_1 ctc_2))
   (→ (ctc->type ctc_1) (ctc->type ctc_2))]
  [(ctc->type (prompt-tag/c ctc_1 ctc_2 t_1 t_2))
   (Prompt (ctc->type ctc_1) (ctc->type ctc_2))]
  [(ctc->type (mark/c ctc t))
   (Mark (ctc->type ctc))]
  [(ctc->type (list/c ctc))
   (List (ctc->type ctc))])

(define-metafunction blame+Γ-lang
  ∈ : any any -> l or #f
  [(∈ (x : l Γ) x) l]
  [(∈ (x_1 : l_1 Γ) x_2)
   (∈ Γ x_2)
   (side-condition (term (different x_1 x_2)))]
  [(∈ (v : l Σ) v) l]
  [(∈ (v_1 : l Σ) v_2)
   (∈ Σ v_2)
   (side-condition (term (different v_1 v_2)))]
  [(∈ · any) #f])

(define-metafunction blame+Γ-lang
  [(different any_1 any_1) #f]
  [(different any_1 any_2) #t])

(module+ test
  (require rackunit)

  (check-true
   (judgment-holds
    (wfsp · · "τ" 0)))
  (check-true
   (judgment-holds
    (wfsp · · "τ" #t)))
  (check-true
   (judgment-holds
    (wfsp · · "τ" (own 0 "τ"))))
  (check-false
   (judgment-holds
    (wfsp · · "τ" (own 0 "υ"))))
  (check-true
   (judgment-holds
    (wfsp · · "τ"
          (cons 0 (null Num)))))
  (check-true
   (judgment-holds
    (wfctc · · ("τ") ("υ") "j"
           (oblig (flat (own (λ (x : Num) (zero? x)) "j")) ("τ")))))
  (check-true
   (judgment-holds
    (wfctci · · ("τ") ("υ") "j"
            (oblig (flat (own (λ (x : Num) (zero? x)) "j")) ("τ" "υ")))))
  (check-equal?
   (term (ctc->type (oblig (flat (own (λ (x : Num) (zero? x)) "j")) ("τ"))))
   'Num)
  (check-equal?
   (term (ctc->type (-> (oblig (flat (own (λ (x : Num) (zero? x)) "j")) ("υ"))
                        (oblig (flat (own (λ (x : Num) (number? x)) "j")) ("τ")))))
   '(→ Num Num))
  (check-true
   (judgment-holds
    (wfst (tag0 : "τ" (key0 : "υ" ·))
          (tag0 (key0 ·)))))
  (check-true
   (judgment-holds
    (lwfp · (x : "τ" ·) "τ" x)))
  (check-false
   (judgment-holds
    (lwfp · (x : "τ" ·) "υ" x)))
  (check-true
   (judgment-holds
    (lwfp · · "τ" ((own (λ (x : Num) x) "τ") 0))))
  (check-true
   (judgment-holds
    (wfip · · "τ"
          (ctc-error "τ" "j"))))
  (check-false
   (judgment-holds
    (wfip · · "τ"
          (check #t ((λ (x : Num) x) 0) "τ" "j"))))
  (check-true
   (judgment-holds
    (wfip · · "τ"
          (monitor (oblig (flat (own (λ (x : Num) (zero? x)) "j")) ("τ" "υ"))
                   ((own (λ (x : Num) x) "τ") 0)
                   "τ" "τ" "j"))))
  (check-true
   (judgment-holds
    (ctcwitnessp
     (monitor (oblig (flat (own (λ (x : Num) (zero? x)) "j")) ("τ"))
              (own 0 "τ")
              "τ" "υ" "j")
     "τ" "j"))))
