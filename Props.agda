module Props where

  open import Data.Product using (_×_; proj₁; proj₂; Σ-syntax)
    renaming (_,_ to _×,_)
  open import Data.List.Relation.Binary.Permutation.Propositional.Properties
    using (↭-length)
  open import Relation.Binary.PropositionalEquality using (_≡_; sym; cong)
    renaming (trans to ≡-trans)

  open import Util
  open import Base

  private variable
    A B : Typ
    Γ Δ Θ : Context

  ↭-cod-partₗ : (Γ ++ Δ) ↭ Θ → Context
  ↭-cod-partᵣ : (Γ ++ Δ) ↭ Θ → Context
  ↭-cod-part : (r : (Γ ++ Δ) ↭ Θ)
             → (↭-cod-partₗ {Γ = Γ} r ++ ↭-cod-partᵣ {Γ = Γ} r ≡ Θ)

  ↭-cod-partₗ {Γ = ε} _ = ε
  ↭-cod-partₗ {Γ = _ , ε} refl = ε
  ↭-cod-partₗ {Γ = _ , ε} (prep _ p) = {!!}
  ↭-cod-partₗ {Γ = _ , ε} (swap _ _ p) = {!!}
  ↭-cod-partₗ {Γ = _ , ε} (trans p p') = {!!}
  ↭-cod-partₗ {Γ = _ , _ , Γ} p = {!!}

  private

    ~>*-refl : Γ ~>* Γ
    ~>*-refl {ε} = null
    ~>*-refl {_ , _} = plus ~>*-refl var

  ~>-refl : Γ ~> Γ
  ~>-refl = _ ×, ~>*-refl ×, refl

  ~>*-cod-partₗ : (Γ ++ Δ) ~>* Θ → Context
  ~>*-cod-partᵣ : (Γ ++ Δ) ~>* Θ → Context
  ~>*-cod-part : (σ* : (Γ ++ Δ) ~>* Θ)
               → (~>*-cod-partₗ {Γ = Γ} σ* ++ ~>*-cod-partᵣ {Γ = Γ} σ* ≡ Θ)

  ~>*-cod-partₗ {Γ = ε} _ = ε
  ~>*-cod-partₗ {Γ = _ , Γ} (plus {Δ' = Δ'} σ* _) =
    Δ' ++ ~>*-cod-partₗ {Γ = Γ} σ*

  ~>*-cod-partᵣ {Γ = ε} {Θ = Θ} _ = Θ
  ~>*-cod-partᵣ {Γ = _ , Γ} (plus σ* _) = ~>*-cod-partᵣ {Γ = Γ} σ*

  ~>*-cod-part {Γ = ε} _ = _≡_.refl
  ~>*-cod-part {Γ = _ , Γ} (plus σ* t) =
    ≡-trans (++-assoc _ IHₗ IHᵣ) (cong (_ ++_) IH) where
    IHₗ = ~>*-cod-partₗ {Γ = Γ} σ*
    IHᵣ = ~>*-cod-partᵣ {Γ = Γ} σ*
    IH = ~>*-cod-part {Γ = Γ} σ*
    open import Data.List.Properties using (++-assoc)

  ~>*-part : (σ* : (Γ ++ Δ) ~>* Θ)
           → (Γ ~>* (~>*-cod-partₗ {Γ = Γ} σ*)) ×
             (Δ ~>* (~>*-cod-partᵣ {Γ = Γ} σ*))
  ~>*-part {Γ = ε} σ* = null ×, σ*
  ~>*-part {Γ = _ , Γ} (plus σ* t) =
    plus (proj₁ IH) t ×, proj₂ IH where
    IH = ~>*-part {Γ = Γ} σ*

  ~>-cod-partₗ : (Γ ++ Δ) ~> Θ → Context
  ~>-cod-partᵣ : (Γ ++ Δ) ~> Θ → Context
  ~>-cod-part : (σ : (Γ ++ Δ) ~> Θ)
              → (~>-cod-partₗ {Γ = Γ} σ ++ ~>-cod-partᵣ {Γ = Γ} σ ≡ Θ)

  ~>-part : (σ : (Γ ++ Δ) ~> Θ)
          → (Γ ~> (~>-cod-partₗ {Γ = Γ} σ)) ×
            (Δ ~> (~>-cod-partᵣ {Γ = Γ} σ))
  ~>-part (_ ×, σ* ×, p) = {!!}

  ↑ : Γ ~> Δ → (A , Γ) ~> (A , Δ)
  ↑ (_ ×, σ* ×, p) = _ ×, plus σ* var ×, prep _ p

  rename : A ⊣ Γ → Γ ↭ Δ → A ⊣ Δ
  rename = perm

  subst : A ⊣ Γ → Γ ~> Δ → A ⊣ Δ
  subst (perm t p) σ = subst t (permₗ σ (↭-sym p)) where
    open import Data.List.Relation.Binary.Permutation.Propositional
      using (↭-sym)
  subst {Δ = Δ} var (_ ×, plus null t ×, p) =
    perm t (transport {B = _↭ Δ} (++-identityʳ _) p) where
    open import Data.List.Properties using (++-identityʳ)
  subst {Δ = Δ} ⊤ (_ ×, null ×, p)
    with empty-list-length {Γ = Δ} (sym (↭-length p))
  ...  | _≡_.refl = ⊤
  subst (abs t) σ = abs (subst t (↑ σ))
  subst {Δ = Θ} (app {Γ = Γ} {Δ} t u) σ = let
    pₗ ×, pᵣ = ~>-part {Γ = Γ} σ in
    transport {B = _ ⊣_} (~>-cod-part {Γ = Γ} σ)
              (app (subst t pₗ) (subst u pᵣ))
  subst {Δ = Θ} (pair {Γ = Γ} {Δ} t u) σ = let
    pₗ ×, pᵣ = ~>-part {Γ = Γ} σ in
    transport {B = _ ⊣_} (~>-cod-part {Γ = Γ} σ)
              (pair (subst t pₗ) (subst u pᵣ))
  subst {Δ = Θ} (split {A} {B} {Γ = Γ} {C} {Δ = Δ} t u) σ = let
    pₗ ×, pᵣ = ~>-part {Γ = Γ} σ in
    transport {B = _ ⊣_} (~>-cod-part {Γ = Γ} σ)
              (split (subst t pₗ) (subst u (↑ (↑ pᵣ))))
