module Base where

  open import Data.Nat using (suc)
  open import Data.Product using (_×_)
  open import Data.List.Relation.Binary.Permutation.Propositional.Properties
    using (↭-length)
  open import Data.List.Relation.Binary.Permutation.Propositional
    using (↭-sym)
  open import Relation.Binary.PropositionalEquality using (_≡_; sym; cong)
    renaming (trans to ≡-trans)

  open import Util

  data Typ : Set

  open import Trans {Typ}

  data _⊣_ : Typ → Context → Set

  private variable
    Γ Γ' Δ Δ' Θ Θ' : Context
    A B C : Typ
    t t' u u' v v' : A ⊣ Γ

  data Typ where
    𝟙 : Typ
    _⊸_ : Typ → Typ → Typ
    _⊗_ : Typ → Typ → Typ

  data _⊣_ where
    perm : A ⊣ Γ → Γ ↭ Δ → A ⊣ Δ
    
    var : A ⊣ (A , ε)
    
    ⊤ : 𝟙 ⊣ ε
    
    abs : B ⊣ (A , Γ)
        → (A ⊸ B) ⊣ Γ
    app : (A ⊸ B) ⊣ Γ → A ⊣ Δ
        → B ⊣ (Γ ++ Δ)

    pair : A ⊣ Γ → B ⊣ Δ
         → (A ⊗ B) ⊣ (Γ ++ Δ)
    split : (A ⊗ B) ⊣ Γ → C ⊣ (A , B , Δ)
          → C ⊣ (Γ ++ Δ)

  open Sub {_⊣_}

  rename : A ⊣ Γ → Γ ↭ Δ → A ⊣ Δ
  rename = perm

  subst : A ⊣ Γ → Γ ~> Δ → A ⊣ Δ
  subst (perm t p) σ = subst t (permₗ σ (↭-sym p))
  subst var (fst Data.Product., plus null x Data.Product., snd) = {!!}
  subst ⊤ σ = {!!}
  subst (abs t) σ = {!!}
  subst (app t t₁) σ = {!!}
  subst (pair t t₁) σ = {!!}
  subst (split t t₁) σ = {!!}

  modus-ponens : (((A ⊸ B) ⊗ A) ⊸ B) ⊣ ε
  modus-ponens = abs (split var (app var var))

  exch₀ : (A , B , Γ) ↭ (B , A , Γ)
  exch₀ = swap _ _ refl

  flip : ((A ⊗ B) ⊸ (B ⊗ A)) ⊣ ε
  flip = abs (split var (rename (pair var var) exch₀))
