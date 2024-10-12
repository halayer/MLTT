{-# OPTIONS --cubical #-}

module Trans {Typ : Set} where

  open import Agda.Builtin.Sigma using () renaming (_,_ to _×,_)

  open import Cubical.Foundations.Prelude
  open import Cubical.Foundations.Function using ()
    renaming (idfun to id)
  open import Cubical.Foundations.Isomorphism using (Iso; isoToEquiv)
  open import Cubical.Foundations.Univalence using (ua)
  open import Cubical.Data.Unit using (Unit; tt)
  open import Cubical.Data.Prod using (_×_; ×≡)
    renaming (_,_ to _×,_)
  --open import Cubical.Data.Sigma using (∃-syntax)
  open import Cubical.HITs.PropositionalTruncation using (∣_∣₁)

  _∘_ : ∀ {𝓁 𝓁' 𝓁''} {A : Set 𝓁} {B : Set 𝓁'} {C : Set 𝓁''}
      → (B → C) → (A → B) → (A → C)
  (g ∘ f) a = g (f a)

  data Context : Set

  private variable
    A B : Typ
    Γ Δ Θ : Context

  data Context where
    ε : Context
    _,_ : Typ → Context → Context
    swap : (A , (B , Γ)) ≡ (B , (A , Γ))
    --trunc : isSet Context

  _++_ : Context → Context → Context
  ε ++ Δ = Δ
  (A , Γ) ++ Δ = A , (Γ ++ Δ)
  swap {A = A} {B = B} {Γ = Γ} i ++ Δ =
    swap {A = A} {B = B} {Γ = Γ ++ Δ} i

  data _∈_ : Typ → Context → Set where
    e0 : A ∈ (A , Γ)
    eS : A ∈ Γ → A ∈ (B , Γ)

  ∈-ind : {C : Set} → A ∈ Γ
        → (Σ[ Δ ∈ Context ] (Γ ≡ (A , Δ)) → C)
        → (∀ {Δ} → A ∈ Δ → C)
        → C
  ∈-ind (e0 {Γ = Γ}) c f = c (Γ ×, refl)
  ∈-ind (eS e) c f = f e

  _↝_ : Context → Context → Set
  Γ ↝ Δ = Γ ≡ Δ

  ↝-refl : Γ ↝ Γ
  ↝-refl = refl

  ↝-trans : Γ ↝ Δ → Δ ↝ Θ → Γ ↝ Θ
  ↝-trans r r' = r ∙ r'

  _∙rr_ : Δ ↝ Θ → Γ ↝ Δ → Γ ↝ Θ
  _∙rr_ r' r = ↝-trans r r'

  module Sub {_⊣_ : Typ → Context → Set} {var : ∀ {A} → A ⊣ (A , ε)} where

    rename : A ⊣ Γ → Γ ↝ Δ → A ⊣ Δ
    rename {A = A} t r = transport (λ i → A ⊣ r i) t

    private

      ×-commᵢ : {A B : Set} → Iso (A × B) (B × A)
      ×-commᵢ .Iso.fun (a ×, b) = (b ×, a)
      ×-commᵢ .Iso.inv (a ×, b) = (b ×, a)
      ×-commᵢ .Iso.rightInv (a ×, b) = refl
      ×-commᵢ .Iso.leftInv (a ×, b) = refl

      ×-assocᵢ : {A B C : Set} → Iso (A × B × C) ((A × B) × C)
      ×-assocᵢ .Iso.fun (a ×, (b ×, c)) = ((a ×, b) ×, c)
      ×-assocᵢ .Iso.inv ((a ×, b) ×, c) = (a ×, (b ×, c))
      ×-assocᵢ .Iso.rightInv ((a ×, b) ×, c) = refl
      ×-assocᵢ .Iso.leftInv (a ×, (b ×, c)) = refl

      Σ-commᵢ : {A : Set} {B : A → Set} {B' : A → Set} {C : A → A → Set}
               → Iso (Σ[ a ∈ A ] (B a × (Σ[ a' ∈ A ] (B' a' × C a a'))))
                     (Σ[ a' ∈ A ] (B' a' × (Σ[ a ∈ A ] (B a × C a a'))))
      Σ-commᵢ .Iso.fun (a ×, ba ×, a' ×, ba' ×, c) = a' ×, (ba' ×, (a ×, (ba ×, c)))
      Σ-commᵢ .Iso.inv (a' ×, ba' ×, a ×, ba ×, c) = a ×, (ba ×, (a' ×, (ba' ×, c)))
      Σ-commᵢ .Iso.rightInv (a ×, ba ×, a' ×, ba' ×, c) = refl
      Σ-commᵢ .Iso.leftInv (a' ×, ba' ×, a ×, ba ×, c) = refl

    _~>_ : Context → Context → Set
    ε ~> Δ = Unit
    (A , Γ) ~> Δ = Σ[ Δ' ∈ Context ] (A ⊣ Δ') × Γ ~> (Δ' ++ Δ)
    swap {A = A} {B = B} {Γ = Γ} i ~> Δ =
      (ua (isoToEquiv (Σ-commᵢ {A = Context}
                               {B = λ Δ → A ⊣ Δ} {B' = λ Δ → B ⊣ Δ}
                               {C = λ Δ' Δ'' → Γ ~> (Δ'' ++ (Δ' ++ Δ))}))) i

    ~>-refl : Γ ~> Γ
    ~>-refl {ε} = tt
    ~>-refl {A , Γ} = (A , ε) ×, var ×, (~>-refl {Γ = Γ})
    ~>-refl {swap i} = {!!}

    ⟨_⟩ : A ⊣ ε → (A , Γ) ~> Γ
    ⟨_⟩ {Γ = Γ} t = ε ×, t ×, ~>-refl {Γ = Γ}
