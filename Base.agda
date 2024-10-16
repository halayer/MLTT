module Base where

  open import Data.Nat using (suc)
  open import Data.Product using (_×_)
  open import Relation.Binary.PropositionalEquality using (_≡_; sym; cong)
    renaming (trans to ≡-trans)

  open import Util

  data Typ : Set

  open import Trans {Typ}

  data _⊣_ : Typ → Context → Set

  private variable
    Γ Γ' Δ Δ' Θ Θ' : Context
    A B C : Typ
    t t' u u' v v' : A ⊣ Γ

  data Typ where
    𝟙 : Typ
    _⊸_ : Typ → Typ → Typ
    _⊗_ : Typ → Typ → Typ

  data _⊣_ where
    perm : A ⊣ Γ → Γ ↭ Δ → A ⊣ Δ
    
    var : A ⊣ (A , ε)
    
    ⊤ : 𝟙 ⊣ ε
    
    abs : B ⊣ (A , Γ)
        → (A ⊸ B) ⊣ Γ
    app : (A ⊸ B) ⊣ Γ → A ⊣ Δ
        → B ⊣ (Γ ++ Δ)

    pair : A ⊣ Γ → B ⊣ Δ
         → (A ⊗ B) ⊣ (Γ ++ Δ)
    split : (A ⊗ B) ⊣ Γ → C ⊣ (A , B , Δ)
          → C ⊣ (Γ ++ Δ)

  open Sub {_⊣_}

  rename : A ⊣ Γ → Γ ↭ Δ → A ⊣ Δ
  rename = perm

  subst : A ⊣ Γ → Γ ~> Δ → A ⊣ Δ
  subst (perm t p) σ = subst t {!!} where
    _∙ₛₚ_ : Δ ~> Θ → Γ ↭ Δ → Γ ~> Θ
    _∙ₛₚ_ {Δ = Δ} {Γ = ε} σ p with empty-list-length {Γ = Δ} (sym (perm-same-len p))
    ...                          | _≡_.refl = σ
    _∙ₛₚ_ {Γ = _ , _} σ refl = σ
    _∙ₛₚ_ {Γ = _ , _} (plus σ t) (prep _ p) = plus (σ ∙ₛₚ p) t
    --_∙ₛₚ_ {Γ = _ , _} (diff σ t) (prep _ p) = diff (σ ∙ₛₚ p) t
    _∙ₛₚ_ {Γ = _ , _} (plus (plus σ t) u) (swap _ _ p) = perm (plus (plus (σ ∙ₛₚ p) u) t) {!!}
    --_∙ₛₚ_ {Γ = _ , _} (plus (diff σ t) u) (swap _ _ p) = {!!}
    --_∙ₛₚ_ {Γ = _ , _} (diff σ t) (swap _ _ p) = {!!}
    _∙ₛₚ_ {Γ = _ , _} σ (trans p p') = {!!}
  subst var (plus null t) = transp {B = _ ⊣_} lemma t where
    transp : {A : Set} {B : A → Set} {a a' : A} → a ≡ a' → B a → B a'
    transp _≡_.refl b = b
    lemma : Γ ≡ Γ ++ ε
    lemma {ε} = _≡_.refl
    lemma {_ , _} = cong (_ ,_) lemma
  subst ⊤ σ = {!!}
  subst (abs t) σ = {!!}
  subst (app t t₁) σ = {!!}
  subst (pair t t₁) σ = {!!}
  subst (split t t₁) σ = {!!}

  modus-ponens : (((A ⊸ B) ⊗ A) ⊸ B) ⊣ ε
  modus-ponens = abs (split var (app var var))

  exch₀ : (A , B , Γ) ↭ (B , A , Γ)
  exch₀ = swap _ _ refl

  flip : ((A ⊗ B) ⊸ (B ⊗ A)) ⊣ ε
  flip = abs (split var (rename (pair var var) exch₀))
