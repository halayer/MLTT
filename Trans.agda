{-# OPTIONS --cubical #-}

module Trans {Typ : Set} where

  open import Agda.Builtin.Sigma using () renaming (_,_ to _×,_)

  open import Cubical.Foundations.Prelude
  open import Cubical.Foundations.Function using ()
    renaming (idfun to id)
  open import Cubical.Foundations.Isomorphism using (Iso; isoToEquiv)
  open import Cubical.Foundations.Univalence using (ua)
  open import Cubical.Data.Empty using () renaming (⊥ to Empty)
  open import Cubical.Data.Unit using (Unit; tt)
  open import Cubical.Data.Nat using (ℕ; zero; suc; _+_)
  open import Cubical.Data.Nat.Order using
    (_<_; zero-≤; suc-≤-suc; ¬-<-zero; pred-≤-pred)
  open import Cubical.Data.Fin using (Fin)
  open import Cubical.Data.Prod using (_×_; ×≡)
    renaming (_,_ to _×,_)
  open import Cubical.Data.Sigma using (fst; snd)
  --open import Cubical.Data.Sigma using (∃-syntax)
  --open import Cubical.HITs.PropositionalTruncation using (∣_∣₁)

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

  len : Context → ℕ
  len ε = zero
  len (_ , Γ) = suc (len Γ)
  len (swap {Γ = Γ} i) = cong {x = len Γ} (λ n → suc (suc n)) refl i

  _++_ : Context → Context → Context
  ε ++ Δ = Δ
  (A , Γ) ++ Δ = A , (Γ ++ Δ)
  swap {A = A} {B = B} {Γ = Γ} i ++ Δ =
    swap {A = A} {B = B} {Γ = Γ ++ Δ} i

  data _∈_ : Typ → Context → Set where
    e0 : A ∈ (A , Γ)
    eS : A ∈ Γ → A ∈ (B , Γ)

  private

    +0≡ : ∀ {n} → n + 0 ≡ n
    +0≡ {zero} = refl
    +0≡ {suc n} = cong suc +0≡

    +1↔suc : ∀ {n} → n + 1 ≡ suc n
    +1↔suc {zero} = refl
    +1↔suc {suc n} = cong suc +1↔suc

    +suc↔suc : ∀ {m n} → m + suc n ≡ suc (m + n)
    +suc↔suc {zero} = refl
    +suc↔suc {suc m} = cong suc +suc↔suc

    0≤n : ∀ {n} → zero < suc n
    0≤n {zero} = zero ×, refl
    0≤n {suc n} = suc n ×, cong suc (+suc↔suc {m = n} {n = 0} ∙ cong suc +0≡)

    lookup : (Γ : Context) → Fin (len Γ) → Typ
    lookup ε (_ ×, p) with ¬-<-zero p
    ...                  | ()
    lookup (A , Γ) (zero ×, p) = A
    lookup (A , Γ) (suc n ×, p) = lookup Γ (n ×, pred-≤-pred p)
    lookup (swap i) (fst₁ ×, snd₁) = {!!} -- Nicht möglich, solange swap enthalten!

    ∈↔ℕ : Iso (A ∈ Γ) (Fin (len Γ))
    ∈↔ℕ .Iso.fun e0 = zero ×, 0≤n
    ∈↔ℕ .Iso.fun (eS e) = helper {e = e} where
      helper : {e : A ∈ Γ} → Fin (suc (len Γ))
      helper {e = e0} = zero ×, suc-≤-suc zero-≤
      helper {e = eS e} = suc (fst (helper {e = e})) ×, suc-≤-suc (snd (helper {e = e}))
    ∈↔ℕ .Iso.inv (zero ×, p) = {!!}
    ∈↔ℕ .Iso.inv (suc n ×, p) = {!!}
    ∈↔ℕ .Iso.rightInv = {!!}
    ∈↔ℕ .Iso.leftInv = {!!}

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

    _~>_ : Context → Context → Set
    Γ ~> Δ = ∀ {A} → A ∈ Γ → A ⊣ Δ

    ~>-refl : Γ ~> Γ
    ~>-refl {ε} e = {!!}
    ~>-refl {A , Γ} e = {!!}
    ~>-refl {swap i} e = {!!}

    ⟨_⟩ : A ⊣ ε → (A , Γ) ~> Γ
    ⟨_⟩ {Γ = Γ} t = {!!}
