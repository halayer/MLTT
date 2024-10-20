{-# OPTIONS --without-K #-}

module Util where

  open import Data.Product using (∃₂; _,_)
  open import Data.List using (List; []; _∷_; length)
  open import Relation.Binary.PropositionalEquality using (_≡_)

  transport : {A : Set} {B : A → Set} {a a' : A} → a ≡ a' → B a → B a'
  transport _≡_.refl b = b

  generalize₂ : {A : Set} {B : A → A → Set} {a b : A} → B a b → ∃₂ B
  generalize₂ b = _ , _ , b

  empty-list-length : {A : Set} {Γ : List A} → length Γ ≡ 0 → Γ ≡ []
  empty-list-length {Γ = []} _≡_.refl = _≡_.refl
  empty-list-length {Γ = _ ∷ _} ()
