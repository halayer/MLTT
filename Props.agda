{-# OPTIONS --allow-unsolved-metas --show-implicit #-}

module Props {P : Set} where

  open import Data.Product using (_×_; proj₁; proj₂; Σ-syntax)
    renaming (_,_ to _×,_)
  open import Data.List.Properties using (++-identityʳ)
  open import Data.List.Relation.Binary.Permutation.Propositional
    using (↭-sym; ↭-trans)
  open import Data.List.Relation.Binary.Permutation.Propositional.Properties
    using (++⁺ˡ; ++⁺ʳ; ++-assoc; ++-comm; ↭-length)
  open import Relation.Binary.PropositionalEquality using (_≡_; sym; cong)
    renaming (trans to ≡-trans)
  import Relation.Binary.PropositionalEquality.Properties
  open Relation.Binary.PropositionalEquality.Properties.≡-Reasoning

  open import Util
  open import Base {P}

  private variable
    A B : Typ
    Γ Γ' Δ Δ' Θ : Context
    t : A ⊣ Γ

  rename : A ⊣ Γ → Γ ↭ Δ → A ⊣ Δ
  rename t refl = t
  rename t = perm t

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

    permₗ* : Γ ~>* Δ → Γ ↭ Γ' → Γ' ~> Δ
    permₗ* σ* refl = _ ×, σ* ×, refl
    permₗ* (plus {Δ = Δ} {Δ' = Δ'} σ* t) (prep _ p) =
      _ ×, plus (proj₁ (proj₂ IH)) t ×, lemma where
      IH = permₗ* σ* p
      lemma : Δ' ++ proj₁ IH ↭ Δ' ++ Δ
      lemma = ++⁺ˡ Δ' (proj₂ (proj₂ IH))
    permₗ* (plus {Δ' = Δ''} (plus {Δ = Δ} {Δ' = Δ'} σ* t) u) (swap _ _ p) =
      _ ×, plus (plus (proj₁ (proj₂ IH)) u) t ×, lemma where
      IH = permₗ* σ* p
      lemma : Δ' ++ Δ'' ++ proj₁ IH ↭ Δ'' ++ Δ' ++ Δ
      lemma = ↭-trans (↭-trans (↭-trans (
        ↭-sym (++-assoc Δ' Δ'' (proj₁ IH)))
        (++⁺ʳ (proj₁ IH) (++-comm Δ' Δ'')))
        (++⁺ˡ (Δ'' ++ Δ') (proj₂ (proj₂ IH))))
        (++-assoc Δ'' Δ' Δ)
    permₗ* {Δ = Δ} σ* (trans p p') =
      _ ×, proj₁ (proj₂ IH) ×, lemma where
      IH' = permₗ* σ* p
      IH = permₗ* (proj₁ (proj₂ IH')) p'
      lemma : proj₁ IH ↭ Δ
      lemma = ↭-trans (proj₂ (proj₂ IH)) (proj₂ (proj₂ IH'))

  permₗ : Γ ~> Δ → Γ ↭ Γ' → Γ' ~> Δ
  permₗ (_ ×, σ* ×, p) p' =
    _ ×, proj₁ (proj₂ σ') ×, ↭-trans (proj₂ (proj₂ σ')) p where
    σ' = permₗ* σ* p'
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
    ≡-trans (Data.List.Properties.++-assoc _ IHₗ IHᵣ) (cong (_ ++_) IH) where
    IHₗ = ~>*-cod-partₗ {Γ = Γ} σ*
    IHᵣ = ~>*-cod-partᵣ {Γ = Γ} σ*
    IH = ~>*-cod-part {Γ = Γ} σ*
    import Data.List.Properties

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
  ↑ (_ ×, σ* ×, refl) = _ ×, plus σ* var ×, refl
  ↑ (_ ×, σ* ×, p) = _ ×, plus σ* var ×, prep _ p

  ↑* : Γ ~>* Δ → (A , Γ) ~>* (A , Δ)
  ↑* σ* = plus σ* var

  ⟨_⟩ : A ⊣ Δ → (A , Γ) ~> (Δ ++ Γ)
  ⟨ t ⟩ = _ ×, plus ~>*-refl t ×, refl

  ⟨_⟩* : A ⊣ Δ → (A , Γ) ~>* (Δ ++ Γ)
  ⟨ t ⟩* = plus ~>*-refl t

  subst : A ⊣ Γ → Γ ~> Δ → A ⊣ Δ
  subst* : A ⊣ Γ → Γ ~>* Δ → A ⊣ Δ

  subst* (perm t p) σ* = subst t (permₗ* σ* (↭-sym p))
  subst* var (plus null t) = transport {B = _ ⊣_} (sym (++-identityʳ _)) t
  subst* (a x) null = a x
  subst* ⊤ null = ⊤
  subst* (abs t) σ* = abs (subst* t (↑* σ*))
  subst* (app {Γ = Γ} t u) σ* = let
    pₗ* ×, pᵣ* = ~>*-part {Γ = Γ} σ* in
    transport {B = _ ⊣_} (~>*-cod-part {Γ = Γ} σ*)
              (app (subst* t pₗ*) (subst* u pᵣ*))
  subst* (pair {Γ = Γ} t u) σ* = let
    pₗ* ×, pᵣ* = ~>*-part {Γ = Γ} σ* in
    transport {B = _ ⊣_} (~>*-cod-part {Γ = Γ} σ*)
              (pair (subst* t pₗ*) (subst* u pᵣ*))
  subst* (split {Γ = Γ} t u) σ* = let
    pₗ* ×, pᵣ* = ~>*-part {Γ = Γ} σ* in
    transport {B = _ ⊣_} (~>*-cod-part {Γ = Γ} σ*)
              (split (subst* t pₗ*) (subst* u (↑* (↑* pᵣ*))))

  subst t (_ ×, σ* ×, p) = rename (subst* t σ*) p

  subst*-refl : subst* t ~>*-refl ≡ t
  subst*-refl {t = t} = {!!}

  private

    ~>**-trans : Γ ~>* Δ → Δ ~>* Θ → Γ ~>* Θ
    ~>**-trans null null = null
    ~>**-trans (plus {Δ' = Δ'} σ* t) ρ* = let
      pₗ ×, pᵣ = ~>*-part {Γ = Δ'} ρ* in
      transport {B = _ ~>*_} (~>*-cod-part {Γ = Δ'} ρ*)
                (plus (~>**-trans σ* pᵣ) (subst* t pₗ))

    ~>*-trans : Γ ~>* Δ → Δ ~> Θ → Γ ~> Θ
    ~>*-trans null (_ ×, null ×, p) = _ ×, null ×, p
    ~>*-trans (plus {Δ' = Δ'} σ* t) ρ@(_ ×, ρ* ×, p) = let
      _ ×, pᵣ* = ~>*-part {Γ = Δ'} ρ*
      pₗ ×, _ = ~>-part {Γ = Δ'} ρ in
      (_ ×, plus (~>**-trans σ* pᵣ*) (subst t pₗ) ×, ~>-cod-part {Γ = Δ'} ρ)

  ~>-trans : Γ ~> Δ → Δ ~> Θ → Γ ~> Θ
  ~>-trans {Δ = Δ} (_ ×, null ×, p) ρ =
    transport {B = _~> _} (empty-list-length {Γ = Δ} (sym (↭-length p))) ρ
  ~>-trans (_ ×, plus {Δ' = Δ'} σ* t ×, p) ρ@(_ ×, ρ* ×, p') = let
    ρ' = permₗ ρ (↭-sym p)
    pₗ ×, pᵣ = ~>-part {Γ = Δ'} ρ'
    _ ×, ρσ* ×, p'' = ~>*-trans σ* pᵣ in
    _ ×, plus ρσ* (subst t pₗ) ×, ↭-trans (++⁺ˡ _ p'') (~>-cod-part {Γ = Δ'} ρ') where
    open import Data.List.Relation.Binary.Permutation.Propositional.Properties
      using (++⁺ˡ)

  _∙ss**_ : Δ ~>* Θ → Γ ~>* Δ → Γ ~>* Θ
  ρ ∙ss** σ = ~>**-trans σ ρ

  _∙ss_ : Δ ~> Θ → Γ ~> Δ → Γ ~> Θ
  ρ ∙ss σ = ~>-trans σ ρ

  plus-⟨⟩ : {t : A ⊣ Γ'} {σ* : Γ ~>* Δ} → plus σ* t ≡ ⟨ t ⟩* ∙ss** ↑* σ*
  plus-⟨⟩ {A} {ε} {t = t} {null} = _≡_.refl
  plus-⟨⟩ {A} {B , Γ'} {t = t} {null} with ~>**-trans null null | sym (cong (B ,_) (++-identityʳ Γ'))
  ... | null | p = ≡-trans (cong (plus null) (sym (transport-lemma {B = A ⊣_} {ba = t} p))) {!!}
  plus-⟨⟩ {A} {B , Γ'} {t = t} {null} = ≡-trans {!!} (transport {B = plus null t ≡_} {!!} (sym (transport-lemma {B = (A , ε) ~>*_} _≡_.refl)))
  -- transport
  -- (≡-trans
  --   (cong (_,_ B)
  --     (Data.List.Properties.++-assoc Γ'
  --       (Props.IHₗ A Base.List.[] ~>*-refl t)
  --       (Props.IHᵣ A Base.List.[] ~>*-refl t)))
  --   (cong ((B , Γ') ++_) (Props.IH A Base.List.[] ~>*-refl t)))
  -- (plus
  --   (~>**-trans _~>*_.null (~>*-part (_~>*_.plus ~>*-refl t) .proj₂))
  --   (subst* var (~>*-part (_~>*_.plus ~>*-refl t) .proj₁)))
  -- of type (A , ε) ~>* ((B , Γ') ++ ε)
