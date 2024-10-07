{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Trans {Typ : Set} where

  open import Agda.Builtin.Sigma using () renaming (_,_ to _×,_)

  open import Cubical.Foundations.Prelude
  open import Cubical.Foundations.Isomorphism using (Iso; isoToEquiv)
  open import Cubical.Foundations.Univalence using (ua)
  open import Cubical.Data.Unit using (Unit)
  open import Cubical.Data.Prod using (_×_; ×≡)
    renaming (_,_ to _×,_)
  --open import Cubical.Data.Sigma using (∃-syntax)
  open import Cubical.HITs.PropositionalTruncation using (∣_∣₁)

  data Context : Set

  private variable
    A B : Typ
    Γ Γ' Δ Δ' : Context

  data Context where
    ε : Context
    _,_ : Typ → Context → Context
    swap : (A , (B , Γ)) ≡ (B , (A , Γ))
    --trunc : isSet Context

  data _∈_ : Typ → Context → Set where
    e0 : A ∈ (A , Γ)
    eS : A ∈ Γ → A ∈ (B , Γ)

  ∈-ind : {C : Set} → A ∈ Γ
        → (Σ[ Δ ∈ Context ] (Γ ≡ (A , Δ)) → C)
        → (∀ {Δ} → A ∈ Δ → C)
        → C
  ∈-ind (e0 {Γ = Γ}) c f = c (Γ ×, refl)
  ∈-ind (eS e) c f = f e

  module Sub {_⊣_ : Typ → Context → Set} where

    private

      ×-commᵢ : {A B : Set} → Iso (A × B) (B × A)
      ×-commᵢ .Iso.fun = λ {(a ×, b) → (b ×, a)}
      ×-commᵢ .Iso.inv = λ {(a ×, b) → (b ×, a)}
      ×-commᵢ .Iso.rightInv (a ×, b) = refl
      ×-commᵢ .Iso.leftInv (a ×, b) = refl

      ×-assocᵢ : {A B C : Set} → Iso (A × B × C) ((A × B) × C)
      ×-assocᵢ .Iso.fun = λ {(a ×, (b ×, c)) → ((a ×, b) ×, c)}
      ×-assocᵢ .Iso.inv = λ {((a ×, b) ×, c) → (a ×, (b ×, c))}
      ×-assocᵢ .Iso.rightInv ((a ×, b) ×, c) = refl
      ×-assocᵢ .Iso.leftInv (a ×, (b ×, c)) = refl

    [_] : Context → Set
    [ ε ] = Unit
    [ A , Γ ] = A ⊣ (A , ε) × [ Γ ]
    [ swap {A = A} {B = B} {Γ = Γ} i ] = --{!!} where
      (×-assoc ∙∙ cong (_× [ Γ ]) ×-comm ∙∙ sym ×-assoc') i where
      ×-comm = ua (isoToEquiv (×-commᵢ {A = A ⊣ (A , ε)} {B = B ⊣ (B , ε)}))
      ×-assoc = ua (isoToEquiv ×-assocᵢ)
      ×-assoc' = ua (isoToEquiv ×-assocᵢ)

    sub : A ∈ Γ → [ Γ ] → A ⊣ Γ
    sub {Γ = ε} ()
    sub {Γ = _ , _} e (t ×, σ) = ∈-ind e
      (λ {(Δ ×, p) → {!!}})
      {!!}
    sub {Γ = swap i} e σ = {!!}
