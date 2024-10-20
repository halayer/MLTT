{-# OPTIONS --without-K #-}

module Base {P : Set} where

  open import Data.Nat using (suc)
  open import Data.Product using (_×_) renaming (_,_ to _×,_)
  open import Data.List.Relation.Binary.Permutation.Propositional.Properties
    using (↭-length)
  open import Data.List.Relation.Binary.Permutation.Propositional
    using (↭-sym)
  open import Relation.Binary.PropositionalEquality using (_≡_; sym; cong)
    renaming (trans to ≡-trans)

  open import Util

  data Typ : Set

  open import Trans {Typ} public

  data _⊣_ : Typ → Context → Set

  private variable
    Γ Γ' Δ Δ' Θ Θ' : Context
    A B C : Typ
    t t' u u' v v' : A ⊣ Γ

  data Typ where
    ℙ : Typ
    𝟙 : Typ
    _⊸_ : Typ → Typ → Typ
    _⊗_ : Typ → Typ → Typ

  data _⊣_ where
    perm : A ⊣ Γ → Γ ↭ Δ → A ⊣ Δ
    
    var : A ⊣ (A , ε)

    a : P → ℙ ⊣ ε
    
    ⊤ : 𝟙 ⊣ ε
    
    abs : B ⊣ (A , Γ)
        → (A ⊸ B) ⊣ Γ
    app : (A ⊸ B) ⊣ Γ → A ⊣ Δ
        → B ⊣ (Γ ++ Δ)

    pair : A ⊣ Γ → B ⊣ Δ
         → (A ⊗ B) ⊣ (Γ ++ Δ)
    split : (A ⊗ B) ⊣ Γ → C ⊣ (A , B , Δ)
          → C ⊣ (Γ ++ Δ)

  open Sub {_⊣_} public
