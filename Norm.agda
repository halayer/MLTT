{-# OPTIONS #-}

module Norm {P : Set} where

  open import Data.Unit using (tt) renaming (⊤ to Unit)
  open import Data.Product using (_×_; ∃-syntax) renaming (_,_ to _×,_)
  open import Data.List.Properties using (++-assoc)
  open import Data.List.Relation.Binary.Permutation.Propositional.Properties
    using (↭-length)
  open import Relation.Binary.PropositionalEquality using (_≡_; sym; cong)
  import Relation.Binary.PropositionalEquality.Properties
  open Relation.Binary.PropositionalEquality.Properties.≡-Reasoning

  open import Util
  open import Base {P}
  open import Props {P}

  private variable
    A B C : Typ
    Γ Γ' Δ : Context
    t t' u u' v : A ⊣ Γ

  data Val : A ⊣ ε → Set where
    a : ∀ {p} → Val (a p)
    ⊤ : Val ⊤
    abs : Val (abs t)
    pair : {t : A ⊣ ε} → Val (pair t u)

  data _↦c_ : {A : Typ} → A ⊣ ε → A ⊣ ε → Set where
    ord : ∀ {p} → Val t → perm t p ↦c t
    λ-β : Val u → app (abs t) u ↦c subst* t ⟨ u ⟩*
    ×-β : Val t → Val u
        → split (pair t u) v ↦c
          (subst* v (plus (plus ~>*-refl u) t))

  data _↦_ : A ⊣ ε → A ⊣ ε → Set where
    here : t ↦c t' → t ↦ t'
    ap : t ↦ t' → app t u ↦ app t' u
    ap' : u ↦ u' → app (abs t) u ↦ app (abs t) u'
    sp : t ↦ t' → split t u ↦ split t' u

  data _↦*_ : A ⊣ ε → A ⊣ ε → Set where
    done : t ↦* t
    step : t ↦ u → u ↦* v → t ↦* v

  ↦cc-det : t ↦c u → t ↦c v → u ≡ v
  ↦cc-det (ord _) (ord _) = _≡_.refl
  ↦cc-det (λ-β _) (λ-β _) = _≡_.refl
  ↦cc-det (×-β _ _) (×-β _ _) = _≡_.refl

  ↦c-det : t ↦c u → t ↦ v → u ≡ v
  ↦c-det c (here c') = ↦cc-det c c'
  ↦c-det (λ-β _) (ap (here ()))
  ↦c-det (λ-β a) (ap' (here ()))
  ↦c-det (λ-β ⊤) (ap' (here ()))
  ↦c-det (λ-β abs) (ap' (here ()))
  ↦c-det (λ-β pair) (ap' (here ()))
  ↦c-det (×-β _ _) (sp (here ()))

  ↦-det : t ↦ u → t ↦ v → u ≡ v
  ↦-det s (here c) = sym (↦c-det c s)
  ↦-det (here c) s = ↦c-det c s
  ↦-det (ap s) (ap s') = cong (λ t → app t _) (↦-det s s')
  ↦-det (ap' s) (ap (here ()))
  ↦-det (ap (here ())) (ap' _)
  ↦-det (ap' s) (ap' s') = cong (app _) (↦-det s s')
  ↦-det (sp s) (sp s') = cong (λ t → split t _) (↦-det s s')

  _⇓_ : A ⊣ ε → A ⊣ ε → Set
  t ⇓ v = Val v × t ↦* v

  _⇓ : A ⊣ ε → Set
  t ⇓ = ∃[ v ] t ⇓ v

  lifts : {E : A ⊣ ε → B ⊣ ε} → (∀ {u u'} → u ↦ u' → E u ↦ E u')
        → t ↦* t' → E t ↦* E t'
  lifts _ done = done
  lifts s (step s' j) = step (s s') (lifts s j)

  SN' SN : A ⊣ ε → Set

  SN' {ℙ} _ = Unit
  SN' {𝟙} _ = Unit
  SN' {A ⊸ B} t = ∀ u → SN u → SN (app t u)
  SN' {A ⊗ B} _ = Unit

  SN t = SN' t × t ⇓

  data SNs : Context → Set where
    null : SNs ε
    plus : SNs Γ → A ⊣ ε → SNs (A , Γ)

  SNs→~>* : SNs Γ → Γ ~>* ε
  SNs→~>* {ε} null = null
  SNs→~>* {_ , _} (plus σ* t) = plus (SNs→~>* σ*) t

  SNs-perm : SNs Γ → Γ ↭ Δ → SNs Δ
  SNs-perm {ε} {Δ} _ p =
    transport {B = SNs} (sym (empty-list-length {Γ = Δ} (sym (↭-length p)))) null
  SNs-perm (plus σ* t) refl = plus σ* t
  SNs-perm (plus σ* t) (prep _ p) = plus (SNs-perm σ* p) t
  SNs-perm (plus (plus σ* t) u) (swap _ _ p) = plus (plus (SNs-perm σ* p) u) t
  SNs-perm (plus σ* t) (trans p p') = SNs-perm (SNs-perm (plus σ* t) p) p'

  sn-pres : t ↦ t' → SN t → SN t'
  sn'-pres : t ↦ t' → SN' t → SN' t'
  sn-pres* : t ↦* t' → SN t → SN t'
  sn-pres' : t ↦ t' → SN t' → SN t
  sn'-pres' : t ↦ t' → SN' t' → SN' t
  sn-pres'* : t ↦* t' → SN t' → SN t

  sn-pres s (sn' ×, (v ×, vv ×, j)) = sn'-pres s sn' ×, v ×, vv ×, backstep s vv j where
    backstep : t ↦ t' → Val u → t ↦* u → t' ↦* u
    backstep (here ()) a done
    backstep (here ()) ⊤ done
    backstep (here ()) abs done
    backstep (here ()) pair done
    backstep s _ (step s' j) = transport {B = _↦* _} (↦-det s' s) j

  sn'-pres {ℙ} _ _ = tt
  sn'-pres {𝟙} _ _ = tt
  sn'-pres {A ⊸ B} s sn' u snu = sn-pres (ap s) (sn' u snu)
  sn'-pres {A ⊗ B} _ _ = tt

  sn-pres* done sn = sn
  sn-pres* (step s j) sn = sn-pres* j (sn-pres s sn)

  sn-pres' s (sn' ×, (v ×, vv ×, j)) = sn'-pres' s sn' ×, v ×, vv ×, step s j

  sn'-pres' {ℙ} _ _ = tt
  sn'-pres' {𝟙} _ _ = tt
  sn'-pres' {A ⊸ B} s sn' u snu = sn-pres' (ap s) (sn' u snu)
  sn'-pres' {A ⊗ B} _ _ = tt

  sn-pres'* done sn = sn
  sn-pres'* (step s j) sn = sn-pres' s (sn-pres'* j sn)
  
  fund-thm : (t : A ⊣ Γ) → (σ : SNs Γ)
           → SN (subst* t (SNs→~>* σ))
           
  abs-sn' : (σ : SNs Γ) → SN' (abs (subst* t (↑* (SNs→~>* σ))))
  abs-sn' {t = t} σ u snu@(_ ×, uv ×, uvv ×, j) = sn-pres'*
    (lifts ap' j)
    (sn-pres'
      (here (λ-β uvv))
      (transport {B = SN} helper (fund-thm t (plus σ uv)))) where
    helper =
      subst* t (plus (SNs→~>* σ) uv)             ≡⟨ {!!} ⟩
      subst* t (⟨ uv ⟩* ∙ss** ↑* (SNs→~>* σ))    ≡⟨ {!!} ⟩
      subst* (subst* t (↑* (SNs→~>* σ))) ⟨ uv ⟩* ∎


  fund-thm (perm {Γ = Γ} t p) null with empty-list-length {Γ = Γ} (↭-length p)
  ... | _≡_.refl = transport {B = SN} {!!} (fund-thm t null)
  fund-thm (perm {Γ = Γ} t p) (plus σ* u) = {!!}
  fund-thm var (plus null t) = transport {B = SN} subst*-refl (fund-thm t null)
  fund-thm (a _) null = tt ×, a _ ×, a ×, done
  fund-thm ⊤ null = tt ×, ⊤ ×, ⊤ ×, done
  fund-thm (abs t) σ = abs-sn' {t = t} σ ×, _ ×, abs ×, done
  fund-thm (app t u) σ = {!!}
  fund-thm (pair t u) σ = {!!}
  fund-thm (split t u) σ = {!!}
