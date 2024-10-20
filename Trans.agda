module Trans {Typ : Set} where

  open import Agda.Builtin.Sigma using () renaming (_,_ to _×,_)

  open import Data.Nat using (suc)
  open import Data.List using (_++_) using (length)
    renaming ([] to ε; _∷_ to _,_) public
  open import Data.Product using (_×_; Σ-syntax; proj₁; proj₂)
  import Data.List.Membership.Propositional
  open import Data.List.Relation.Unary.Any using (here; there)
  import Data.List.Relation.Binary.Permutation.Propositional
  open import Relation.Binary.PropositionalEquality
    using (_≡_; refl; sym; cong) renaming (trans to ≡-trans)

  open import Util

  Context = Data.List.List Typ

  private variable
    A B : Typ
    Γ Γ' Δ Δ' : Context

  open Data.List.Membership.Propositional using (_∈_) public
  open Data.List.Relation.Binary.Permutation.Propositional
    using (_↭_; refl; prep; swap; trans) public

  ren : A ∈ Γ → Γ ↭ Δ → A ∈ Δ
  ren (here refl) _↭_.refl = here refl
  ren (here refl) (_↭_.prep _ _) = here refl
  ren (here refl) (_↭_.swap _ _ _) = there (here refl)
  ren (here refl) (_↭_.trans r r') = ren (ren (here refl) r) r'
  ren (there e) _↭_.refl = there e
  ren (there e) (_↭_.prep _ r) = there (ren e r)
  ren (there (here refl)) (_↭_.swap _ _ _) = here refl
  ren (there (there e)) (_↭_.swap _ _ r) = there (there (ren e r))
  ren (there e) (_↭_.trans r r') = ren (ren (there e) r) r'

  module Sub {_⊣_ : Typ → Context → Set} where

    data _~>*_ : Context → Context → Set where
      null : ε ~>* ε
      plus : Γ ~>* Δ → A ⊣ Δ' → (A , Γ) ~>* (Δ' ++ Δ)

    _~>_ : Context → Context → Set
    Γ ~> Δ = Σ[ Δ' ∈ Context ] (Γ ~>* Δ') × (Δ' ↭ Δ)

    private

      lkp-cod* : Γ ~>* Δ → A ∈ Γ → Context
      lkp-cod* (plus {Δ' = Δ'} _ _) (here _) = Δ'
      lkp-cod* (plus σ* _) (there e) = lkp-cod* σ* e

    lkp-cod : Γ ~> Δ → A ∈ Γ → Context
    lkp-cod (_ ×, σ* ×, p) e = lkp-cod* σ* e

    sub : (e : A ∈ Γ) → (σ : Γ ~> Δ) → A ⊣ (lkp-cod σ e)
    sub e (_ ×, σ* ×, p) = sub* e σ* where
      sub* : (e : A ∈ Γ) → (σ* : Γ ~>* Δ) → A ⊣ (lkp-cod* σ* e)
      sub* (here refl) (plus _ t) = t
      sub* (there e) (plus σ* _) = sub* e σ*
