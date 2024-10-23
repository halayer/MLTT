{-# OPTIONS --cubical-compatible #-}

module Util where

  open import Level using (Level)
  open import Data.List using (List; []; _∷_; length)
  open import Function.Definitions using (Injective)
  open import Relation.Binary.PropositionalEquality using (_≡_)

  private variable
    𝓁 𝓁' : Level
    A C : Set 𝓁
    B : A → Set 𝓁'

  transport : {A : Set} {B : A → Set} {a a' : A} → a ≡ a' → B a → B a'
  transport _≡_.refl b = b

  transport-lemma : {a a' : A} {ba : B a} → (p : a ≡ a')
                  → transport p ba ≡ ba
  transport-lemma _≡_.refl = _≡_.refl

  empty-list-length : {A : Set} {Γ : List A} → length Γ ≡ 0 → Γ ≡ []
  empty-list-length {Γ = []} _≡_.refl = _≡_.refl
  empty-list-length {Γ = _ ∷ _} ()
