{-# OPTIONS --allow-unsolved-metas #-}

module Trans {Typ : Set} where

  open import Agda.Builtin.Sigma using () renaming (_,_ to _×,_)

  open import Data.Empty using () renaming (⊥ to Empty)
  open import Data.List using (_++_) renaming ([] to ε; _∷_ to _,_) public
  --import Data.List.Membership.Propositional
  import Data.List.Relation.Binary.Permutation.Propositional

  Context = Data.List.List Typ

  private variable
    A B : Typ
    Γ Γ' Δ Θ : Context

  --open Data.List.Membership.Propositional using (_∈_)
  open Data.List.Relation.Binary.Permutation.Propositional using (_↭_) public

  module Sub {_⊣_ : Typ → Context → Set}
             {var : ∀ {A} → A ⊣ (A , ε)}
             {ex : ∀ {A B C} → C ⊣ (A , B , Γ) → C ⊣ (B , A , Γ)} where

    rename : A ⊣ Γ → Γ ↭ Δ → A ⊣ Δ
    rename {A = A} t _↭_.refl = t
    rename {A = A} t (_↭_.prep x r) = {!!}
    rename {A = A} t (_↭_.swap x y r) = {!!}
    rename {A = A} t (_↭_.trans r r') = {!!}

    --_~>_ : Context → Context → Set
