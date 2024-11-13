{-# OPTIONS --cubical-compatible #-}

module Util where

  open import Level using (Level; suc)
  open import Data.List using (List; []; _∷_; length)
  open import Function.Definitions using (Injective)
  open import Relation.Binary.PropositionalEquality using (_≡_)

  private variable
    𝓁 : Level
    A : Set 𝓁

  empty-list-length : {A : Set} {Γ : List A} → length Γ ≡ 0 → Γ ≡ []
  empty-list-length {Γ = []} _≡_.refl = _≡_.refl
  empty-list-length {Γ = _ ∷ _} ()
