module Contexts (Ty : Set) where

data Con : Set where
  ε   : Con
  _<_ : Con → Ty → Con

_<<_ : Con → Con → Con
Γ << ε = Γ
Γ << (Δ < τ) = (Γ << Δ) < τ

data Var : Con → Ty → Set where
  vz : ∀ {Γ σ} → Var (Γ < σ) σ
  vs : ∀ {Γ σ τ} → Var Γ σ → Var (Γ < τ) σ

