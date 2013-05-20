import STLC
import Types

module Syntax (T : Set) (L : Types.Ty T → Set) where

module SynCalculus = STLC T L
open SynCalculus

infixl 8 _>_ _<_ _⊙>_ _<⊙_
data DTm : Ty → Set where
  `_   : ∀ {σ} → L σ → DTm σ
  _>_  : ∀ {σ τ} → DTm (σ ⇒ τ) → DTm σ → DTm τ
  _<_  : ∀ {σ τ} → DTm σ → DTm (σ ⇒ τ) → DTm τ
  _⊙>_ : ∀ {ρ σ τ} → DTm (σ ⇒ τ) → DTm (ρ ⇒ σ) → DTm (ρ ⇒ τ)
  _<⊙_ : ∀ {ρ σ τ} → DTm (ρ ⇒ σ) → DTm (σ ⇒ τ) → DTm (ρ ⇒ τ)

data DTmR : Ty → Set where
  `_  : ∀ {σ} → L σ → DTmR σ
  _∙_ : ∀ {σ τ} → DTmR (σ ⇒ τ) → DTmR σ → DTmR τ
  _⊙_ : ∀ {ρ σ τ} → DTmR (σ ⇒ τ) → DTmR (ρ ⇒ σ) → DTmR (ρ ⇒ τ)

⟦_⟧⇔ : ∀ {σ} → DTm σ → DTmR σ
⟦ ` x    ⟧⇔ = ` x
⟦ f > x  ⟧⇔ = ⟦ f ⟧⇔ ∙ ⟦ x ⟧⇔
⟦ x < f  ⟧⇔ = ⟦ f ⟧⇔ ∙ ⟦ x ⟧⇔
⟦ f ⊙> g ⟧⇔ = ⟦ f ⟧⇔ ⊙ ⟦ g ⟧⇔
⟦ g <⊙ x ⟧⇔ = ⟦ x ⟧⇔ ⊙ ⟦ g ⟧⇔

⟦_⟧λ : ∀ {σ} → DTmR σ → Tm σ
⟦ ` x   ⟧λ = ` x
⟦ f ∙ x ⟧λ = ⟦ f ⟧λ ∙ ⟦ x ⟧λ
⟦ f ⊙ g ⟧λ = ƛ x ⇒ ⟦ f ⟧λ ∙ (⟦ g ⟧λ ∙ var x)

interpret : ∀ {σ} → DTm σ → Tm σ
interpret x = ⟦ ⟦ x ⟧⇔ ⟧λ
