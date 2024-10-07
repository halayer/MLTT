module Props where

  open import Data.Empty using () renaming (⊥ to Empty)
  --open import Data.Nat using ()
  open import Data.Fin using (Fin; zero; suc)
  open import Data.List using (lookup; length)
  open import Data.Product using (proj₁; proj₂) renaming (_,_ to _×,_)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
  open import Relation.Nullary.Negation using (¬_)
  open import Function.Base using (id; _∘_)
  open import Function.Definitions using (Surjective)
  open import Function.Bundles using (Bijection)
  open import Function.Properties.Bijection using (sym-≡)
  open Bijection

  open import Base
  open import Trans {Typ}
  open Sub {_⊣_}

  private variable
    A B : Typ
    Γ Γ' Δ Δ' Θ : Context
    t : A ⊣ Γ
    w : A ⊣* Γ ↝ Δ

  private
    transp : ∀ {l l'} {A : Set l} {B : A → Set l'} {a b : A}
         → a ≡ b → B a → B b
    transp refl x = x

    empty-elim-not-surjective : {A : Set}
      → (f : Fin 0 → A) (a : A)
      → ¬(Surjective _≡_ _≡_ f)
    empty-elim-not-surjective f a s with (s a)
    ...                                | (() ×, _)

  ↝-sym : Γ ↝ Δ → Δ ↝ Γ
  ↝-sym {Γ = Γ} {Δ = Δ} (r ×, p) =
    (sym-≡ r ×,
     λ n → transp {B = λ i → lookup Δ i ≡ lookup Γ (mapping (sym-≡ r) n)}
       (helper {Γ = Γ} {Δ} {n} {r}) (sym (p (mapping (sym-≡ r) n)))) where
    helper'' : ∀ {Γ} → ¬(Reordering (A , Γ) ε)
    helper'' record {to = m; bijective = m-bi} with m zero
    ...                                           | ()
    helper' : ∀ {Γ} → ¬(Reordering ε (A , Γ))
    helper' record {to = m; bijective = m-bi} =
      empty-elim-not-surjective m zero (m-bi .proj₂)
    helper : ∀ {Γ Δ} → {n : Fin (length Δ)} {r : Reordering Γ Δ}
           → mapping r (mapping (sym-≡ r) n) ≡ n
    helper {Γ = ε} {ε} {n = ()}
    helper {Γ = ε} {A , Δ} {r = r} with helper' {A = A} {Γ = Δ} r
    ...                               | ()
    helper {Γ = A , Γ} {ε} {r = r} with helper'' {A = A} {Γ = Γ} r
    ...                               | ()
    helper {Γ = A , Γ} {B , Δ} {n} {r} =
      r .bijective .proj₂ n .proj₂ refl

  ↝-trans : Γ ↝ Δ → Δ ↝ Θ → Γ ↝ Θ
  ↝-trans
    ((record {to = m; cong = m-cong; bijective = m-bi}) ×, p)
    ((record {to = m'; cong = m'-cong; bijective = m'-bi}) ×, p') =
    record {
      to = m' ∘ m;
      cong = λ {_ _} z → m'-cong (m-cong z);
      bijective =
         (λ {_ _} z → m-bi .proj₁ (m'-bi .proj₁ z)) ×,
         (λ y →
            m-bi .proj₂ (m'-bi .proj₂ y .proj₁) .proj₁ ×,
            (λ {_} z →
               m'-bi .proj₂ y .proj₂
               (m-bi .proj₂ (m'-bi .proj₂ y .proj₁) .proj₂ z)))
     } ×, λ n → trans (p n) (p' (m n))

  _∙rr_ : Δ ↝ Θ → Γ ↝ Δ → Γ ↝ Θ
  _∙rr_ {Δ = Δ} {Θ = Θ} {Γ = Γ} r' r =
    ↝-trans {Γ = Γ} {Δ = Δ} {Θ = Θ} r r'

  rename : A ⊣* Γ ↝ Δ → Γ ↝ Γ' → A ⊣* Γ' ↝ Δ
  rename {Γ = Γ} {Δ = Δ} {Γ' = Γ'} (t ×, r) r' =
    (t ×, (_∙rr_ {Δ = Γ} {Θ = Δ} {Γ = Γ'}
                 r (↝-sym {Γ = Γ} {Δ = Γ'} r')))

  ↝-refl : Γ ↝ Γ
  ↝-refl = record {to = id; cong = λ {_ _} → id;
    bijective = (λ {_ _} → id) ×, (λ y → y ×, (λ {_} → id))} ×,
    (λ _ → refl)

  subst : A ⊣* Γ ↝ Δ → Δ ~> Δ' → A ⊣* Γ ↝ Δ'
  subst (t ×, r) none = {!!}
  subst (t ×, r) (some u σ) = {!!}

  ~>-refl : Γ ~> Γ
  ~>-refl {ε} = none
  ~>-refl {A , Γ} = some var ~>-refl
