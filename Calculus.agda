{-# OPTIONS --no-termination-check #-}
{-# OPTIONS --no-positivity-check #-}

module Calculus (T : Set) where

open import Kit.Equality
open import Kit.Utility
open import Kit.Empty
open import Kit.Either
open import Kit.Maybe
open import Kit.Bool

infixr 8 _⇒_
data Ty : Set where
  ⟨_⟩ : T → Ty
  _⇒_ : Ty → Ty → Ty

-- Cribbed from http://code.haskell.org/~dolio/agda-share/PHOASNorm.agda
module Lambda (Axiom : Ty → Set) where

  module Terms (V : Ty → Set) where
    -- Lambda terms may be axioms, variables, applications and abstractions.
    data Term : Ty → Set where
      `_  : ∀ {τ} → Axiom τ → Term τ
      var : ∀ {τ} → V τ → Term τ
      lam : ∀ {σ τ} → (V σ → Term τ) → Term (σ ⇒ τ)
      _∙_ : ∀ {σ τ} → Term (σ ⇒ τ) → Term σ → Term τ

    infixl 8 _∙_
    syntax lam (λ x → B) = ƛ x ⇒ B

  open Terms public

  Tm : Ty → Set₁
  Tm τ = ∀ {V} → Term V τ
  
  data Closed : Ty → Set where
    `_  : ∀ {τ} → Axiom τ → Closed τ
    _∙_ : ∀ {σ τ} → Closed (σ ⇒ τ) → Closed σ → Closed τ

  data Var (V : Ty → Set) (τ : Ty) : Set where
    vz : V τ → Var V τ
    vs : Term (Var V) τ → Var V τ
  
  norm : ∀ {V τ} → Term (Var V) τ → Term (Var V) τ
  norm (` x)        = ` x
  norm (var (vz x)) = var (vz x)
  norm (var (vs v)) = norm v
  norm (f ∙ x) with norm f
  ... | var (vs v) = norm (v ∙ x)
  ... | lam e      = norm (e (vs x))
  ... | f'         = f' ∙ norm x
  norm (lam e)      = ƛ x ⇒ norm (e x)

  cut : ∀ {V τ} → Term (Var V) τ → Term V τ
  cut (` x)        = ` x
  cut (var (vz x)) = var x
  cut (var (vs e)) = cut e
  cut (f ∙ x)      = cut f ∙ cut x
  cut (lam e)      = ƛ x ⇒ cut (e (vz x))

  normalize : ∀ {τ} → Tm τ → Tm τ
  normalize t = cut (norm t)


  closed? : ∀ {V τ} → Term V τ → Maybe (Closed τ)
  closed? (` x) = just (` x)
  closed? (var x) = nothing
  closed? (lam x) = nothing
  closed? (f ∙ x) = _∙_ <$> closed? f ⊛ closed? x

  closed : ∀ {V τ} (e : Term V τ) {c : Closed τ} {p : closed? e ≅ just c} → Closed τ
  closed e {c} = c

  ⟦_⟧≅_ : ∀ {τ} → Tm τ → Tm τ → Set₁
  ⟦ tm ⟧≅ nm = ∀ {V} → normalize tm {V} ≅ nm {V}
