module Props {P : Set} where

  open import Data.Product using (_×_; proj₁; proj₂; Σ-syntax)
    renaming (_,_ to _×,_)
  open import Data.List.Relation.Binary.Permutation.Propositional
    using (↭-sym; ↭-trans)
  open import Data.List.Relation.Binary.Permutation.Propositional.Properties
    using (↭-length)
  open import Relation.Binary.PropositionalEquality using (_≡_; sym; cong)
    renaming (trans to ≡-trans)

  open import Util
  open import Base {P}

  private variable
    A B : Typ
    Γ Γ' Δ Δ' Θ : Context

  private

    ~>*-refl : Γ ~>* Γ
    ~>*-refl {ε} = null
    ~>*-refl {_ , _} = plus ~>*-refl var

  ~>-refl : Γ ~> Γ
  ~>-refl = _ ×, ~>*-refl ×, refl

  permᵣ : Γ ~> Δ → Δ ↭ Δ' → Γ ~> Δ'
  permᵣ (_ ×, σ* ×, p) p' = _ ×, σ* ×, ↭-trans p p' where
    open import Data.List.Relation.Binary.Permutation.Propositional
      using (↭-trans)

  private

    ppermₗ* : Γ ~>* Δ → Γ ↭ Γ' → Γ' ~> Δ
    ppermₗ* σ* refl = _ ×, σ* ×, refl
    ppermₗ* (plus {Δ = Δ} {Δ' = Δ'} σ* t) (prep _ p) =
      _ ×, plus (proj₁ (proj₂ IH)) t ×, lemma where
      IH = ppermₗ* σ* p
      open import Data.List.Relation.Binary.Permutation.Propositional.Properties
        using (++⁺ˡ)
      lemma : Δ' ++ proj₁ IH ↭ Δ' ++ Δ
      lemma = ++⁺ˡ Δ' (proj₂ (proj₂ IH))
    ppermₗ* (plus {Δ' = Δ''} (plus {Δ = Δ} {Δ' = Δ'} σ* t) u) (swap _ _ p) =
      _ ×, plus (plus (proj₁ (proj₂ IH)) u) t ×, lemma where
      IH = ppermₗ* σ* p
      open import Data.List.Relation.Binary.Permutation.Propositional
        using (↭-sym; ↭-trans)
      open import Data.List.Relation.Binary.Permutation.Propositional.Properties
        using (++⁺ʳ; ++⁺ˡ; ++-assoc; ++-comm)
      lemma : Δ' ++ Δ'' ++ proj₁ IH ↭ Δ'' ++ Δ' ++ Δ
      lemma = ↭-trans (↭-trans (↭-trans (
        ↭-sym (++-assoc Δ' Δ'' (proj₁ IH)))
        (++⁺ʳ (proj₁ IH) (++-comm Δ' Δ'')))
        (++⁺ˡ (Δ'' ++ Δ') (proj₂ (proj₂ IH))))
        (++-assoc Δ'' Δ' Δ)
    ppermₗ* {Δ = Δ} σ* (trans p p') =
      _ ×, proj₁ (proj₂ IH) ×, lemma where
      IH' = ppermₗ* σ* p
      IH = ppermₗ* (proj₁ (proj₂ IH')) p'
      open import Data.List.Relation.Binary.Permutation.Propositional
        using (↭-trans)
      lemma : proj₁ IH ↭ Δ
      lemma = ↭-trans (proj₂ (proj₂ IH)) (proj₂ (proj₂ IH'))

  permₗ : Γ ~> Δ → Γ ↭ Γ' → Γ' ~> Δ
  permₗ (_ ×, σ* ×, p) p' =
    _ ×, proj₁ (proj₂ σ') ×, ↭-trans (proj₂ (proj₂ σ')) p where
    σ' = ppermₗ* σ* p'
    open import Data.List.Relation.Binary.Permutation.Propositional
      using (↭-trans)

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
              → (~>-cod-partₗ {Γ = Γ} σ ++ ~>-cod-partᵣ {Γ = Γ} σ ↭ Θ)

  ~>-cod-partₗ {Γ = Γ} (_ ×, σ* ×, _) = ~>*-cod-partₗ {Γ = Γ} σ*
  
  ~>-cod-partᵣ {Γ = Γ} (_ ×, σ* ×, _) = ~>*-cod-partᵣ {Γ = Γ} σ*

  ~>-cod-part {Γ = Γ} (_ ×, σ* ×, p) =
    transport {B = _↭ _} (sym (~>*-cod-part {Γ = Γ} σ*))
              p

  ~>-part : (σ : (Γ ++ Δ) ~> Θ)
          → (Γ ~> (~>-cod-partₗ {Γ = Γ} σ)) ×
            (Δ ~> (~>-cod-partᵣ {Γ = Γ} σ))
  ~>-part {Γ = ε} σ@(_ ×, σ* ×, p) =
    (_ ×, null ×, refl) ×, _ ×, σ* ×, ↭-trans p (↭-sym (~>-cod-part {Γ = ε} σ))
  ~>-part {Γ = _ , Γ} (_ ×, plus σ* t ×, p) = let
    pₗ ×, pᵣ = ~>*-part {Γ = Γ} σ* in -- Induction Hypothesis
    (_ ×, plus pₗ t ×, refl) ×, _ ×, pᵣ ×, refl

  ↑ : Γ ~> Δ → (A , Γ) ~> (A , Δ)
  ↑ (_ ×, σ* ×, p) = _ ×, plus σ* var ×, prep _ p

  rename : A ⊣ Γ → Γ ↭ Δ → A ⊣ Δ
  rename = perm

  subst : A ⊣ Γ → Γ ~> Δ → A ⊣ Δ
  subst (perm t p) σ = subst t (permₗ σ (↭-sym p)) where
    open import Data.List.Relation.Binary.Permutation.Propositional
      using (↭-sym)
  subst {Δ = Δ} (a P) (_ ×, null ×, p)
    with empty-list-length {Γ = Δ} (sym (↭-length p))
  ... | _≡_.refl = a P
  subst {Δ = Δ} var (_ ×, plus null t ×, p) =
    perm t (transport {B = _↭ Δ} (++-identityʳ _) p) where
    open import Data.List.Properties using (++-identityʳ)
  subst {Δ = Δ} ⊤ (_ ×, null ×, p)
    with empty-list-length {Γ = Δ} (sym (↭-length p))
  ...  | _≡_.refl = ⊤
  subst (abs t) σ = abs (subst t (↑ σ))
  subst {Δ = Θ} (app {Γ = Γ} {Δ} t u) σ = let
    pₗ ×, pᵣ = ~>-part {Γ = Γ} σ in
    perm (app (subst t pₗ) (subst u pᵣ))
         (~>-cod-part {Γ = Γ} σ)
  subst {Δ = Θ} (pair {Γ = Γ} {Δ} t u) σ = let
    pₗ ×, pᵣ = ~>-part {Γ = Γ} σ in
    perm (pair (subst t pₗ) (subst u pᵣ))
          (~>-cod-part {Γ = Γ} σ)
  subst {Δ = Θ} (split {A} {B} {Γ = Γ} {C} {Δ = Δ} t u) σ = let
    pₗ ×, pᵣ = ~>-part {Γ = Γ} σ in
    perm (split (subst t pₗ) (subst u (↑ (↑ pᵣ))))
         (~>-cod-part {Γ = Γ} σ)
