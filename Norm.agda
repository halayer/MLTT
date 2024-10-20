{-# OPTIONS #-}

module Norm {P : Set} where

  open import Data.Product using () renaming (_,_ to _×,_)
  open import Data.List.Properties using (++-assoc)
  open import Relation.Binary.PropositionalEquality using (_≡_; sym)

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
    step : t ↦ v → u ↦* v → t ↦* v

  ↦cc-det : t ↦c u → t ↦c v → u ≡ v
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
