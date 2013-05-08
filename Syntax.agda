open import Calculus

module Syntax (T : Set) (L : Ty T → Set) where

module SynCalculus = Lambda T L
open SynCalculus

infixl 8 _>_ _<_ _⊙>_ _<⊙_
data DTm : Ty T → Set where
  `_   : ∀ {σ} → L σ → DTm σ
  _>_  : ∀ {σ τ} → DTm (σ ⇒ τ) → DTm σ → DTm τ
  _<_  : ∀ {σ τ} → DTm σ → DTm (σ ⇒ τ) → DTm τ
  _⊙>_ : ∀ {ρ σ τ} → DTm (σ ⇒ τ) → DTm (ρ ⇒ σ) → DTm (ρ ⇒ τ)
  _<⊙_ : ∀ {ρ σ τ} → DTm (ρ ⇒ σ) → DTm (σ ⇒ τ) → DTm (ρ ⇒ τ)

data DTmR : Ty T → Set where
  `_  : ∀ {σ} → L σ → DTmR σ
  _∙_ : ∀ {σ τ} → DTmR (σ ⇒ τ) → DTmR σ → DTmR τ
  _⊙_ : ∀ {ρ σ τ} → DTmR (σ ⇒ τ) → DTmR (ρ ⇒ σ) → DTmR (ρ ⇒ τ)

erase-dir : ∀ {σ} → DTm σ → DTmR σ
erase-dir (` x) = ` x
erase-dir (f > x) = erase-dir f ∙ erase-dir x
erase-dir (x < f) = erase-dir f ∙ erase-dir x
erase-dir (f ⊙> g) = erase-dir f ⊙ erase-dir g
erase-dir (g <⊙ x) = erase-dir x ⊙ erase-dir g

to-lambda : ∀ {Γ σ} → DTmR σ → Tm Γ σ
to-lambda (` x) = ` x
to-lambda (f ∙ x) = to-lambda f ∙ to-lambda x
to-lambda (f ⊙ g) = ƛ (to-lambda f ∙ (to-lambda g ∙ var vz))

interpret : ∀ {Γ σ} → DTm σ → Tm Γ σ
interpret x = to-lambda (erase-dir x)
