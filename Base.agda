module Base where

  open import Data.Product using (_×_)

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

  --modus-ponens : ((A ⊸ B) ⊸ (A ⊸ B)) ⊣ ε
  --modus-ponens = abs (abs (app var var))

  -- Problem: Wie kriegen wir ex heraus?
  flip : ((A ⊗ B) ⊸ (B ⊗ A)) ⊣ ε
  flip {A} {B} = abs (split var (ex (var {A = B}) (var {A = A})))

  norm : (𝟙 ⊗ (𝟙 ⊸ 𝟙)) ⊣ ε
  norm = app flip (pair (abs var) ⊤)
