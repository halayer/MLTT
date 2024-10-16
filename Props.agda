module Props where

  open import Base

  ~>-refl : Γ ~> Γ
  ~>-refl {ε} = null
  ~>-refl {_ , _} = plus ~>-refl var

  ~>-trans : Γ ~> Δ → Δ ~> Θ → Γ ~> Θ
  ~>-trans {Γ = ε} r r' = null
  ~>-trans {Γ = _ , _} (plus {Δ = ε} {Δ' = ε} r t) r' = plus (~>-trans r r') t
  ~>-trans {Γ = _ , _} (plus {Δ = ε} {Δ' = _ , _} r t) (plus {Δ = ε} r' u) = plus r {!!}
  ~>-trans {Γ = _ , _} (plus {Δ = ε} {Δ' = _ , _} r t) (plus {Δ = _ , _} r' u) = {!!}
  ~>-trans {Γ = _ , _} (plus {Δ = x , Δ} r t) r' = {!!}
