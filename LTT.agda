module LTT where

  open import Data.Empty using () renaming (⊥ to Empty)
  open import Data.Unit using (tt) renaming (⊤ to Unit)
  open import Data.Nat using () renaming (ℕ to Nat)
  open import Data.List using (List; _++_; length) renaming ([] to ε; _∷_ to _,_)
  open import Data.Product using (Σ; _×_) renaming (_,_ to _×,_)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl)
  open import Function.Bundles using (Bijection)

  -- Umbenennungen sind bijektiv
  rename : A ⊣ Γ → Γ ↝ Δ → A ⊣ Δ

  -- Substitutionen

  ~>-refl : Γ ~> Γ
  ~>-refl {Γ = ε} = none
  ~>-refl {Γ = A , Γ} = funct (some var) ~>-refl

  --_~>_ : Context → Context → Set
  --_~>_ ε Δ = Unit
  --_~>_ (A , Γ) Δ =
  
  --[_] : Context → Set
  --[ ε ] = Unit
  --[ A , Γ ] = A ⊣ ε × [ Γ ]

  
  subst : A ⊣ Γ → Γ ~> Δ → A ⊣ Δ

  data Val : A ⊣ Γ → Set where
    singleton : Val T
    true : Val ⊤
    false : Val ⊥
    lam : Val (abs t)
    pair : Val (pair t u)

  data _↦c_ : A ⊣ Γ → A ⊣ Γ → Set where
    η : t ↦c T
    if-⊤ : (rec-𝟚 ⊤ t u) ↦c t
    if-⊥ : (rec-𝟚 ⊥ t u) ↦c u
    β : {t : B ⊣ (A , Γ)} {u : A ⊣ Δ}
      → Val u → app (abs t) u ↦c subst t {!!}

  data _↦_ : A ⊣ Γ → A ⊣ Γ → Set where
