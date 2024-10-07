{-# OPTIONS --cubical #-}

module Base {P : Set} where

  open import Cubical.Foundations.Prelude

  data Typ : Set

  open import Trans {Typ}

  data _⊣_ : Typ → Context → Set

  private variable
    Γ Γ' Δ Δ' Θ Θ' : Context
    A B C : Typ
    t t' u u' v v' : A ⊣ Γ

  data Typ where
    ℙ : Typ
    𝟙 : Typ
    _⊸_ : Typ → Typ → Typ
    _⊗_ : Typ → Typ → Typ
    trunc : isSet Typ

  data _⊣_ where
    ex : A ⊣ (B , C , Γ)
       → A ⊣ (C , B , Γ)
    var : A ⊣ (A , ε)

    p : P → ℙ ⊣ (ℙ , ε)
    
    T : 𝟙 ⊣ (𝟙 , ε)
    
    abs : B ⊣ (A , Γ)
        → (A ⊸ B) ⊣ Γ
    app : (A ⊸ B) ⊣ Γ → A ⊣ Δ
        → B ⊣ (Γ ++ Δ)
    --app : (A ⊸ B) ⊣ Γ
    --    → B ⊣ (A , Γ)

    pair : A ⊣ Γ → B ⊣ Δ
         → (A ⊗ B) ⊣ (Γ ++ Δ)
    split : (A ⊗ B) ⊣ Γ → C ⊣ (A , B , Δ)
          → C ⊣ (Γ ++ Δ)

  --modus-ponens : ((A ⊸ B) ⊸ (A ⊸ B)) ⊣ ε
  --modus-ponens = abs (abs (app var var))

  -- Problem: Wie kriegen wir ex heraus?
  swap : ((A ⊗ B) ⊸ (B ⊗ A)) ⊣ ε
  swap = abs (split var (ex (pair var var)))
