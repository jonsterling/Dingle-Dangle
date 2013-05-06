open import Calculus

module Syntax (T : Set) (L : Ty T → Set) where
open Lambda T L

infixl 8 _>_ _<_ _⊙>_ _<⊙_
data DTm : Ty T → Set where
  `_   : ∀ {σ} → L σ → DTm σ
  _>_  : ∀ {σ τ} → DTm (σ ⇒ τ) → DTm σ → DTm τ
  _<_  : ∀ {σ τ} → DTm σ → DTm (σ ⇒ τ) → DTm τ
  _⊙>_ : ∀ {ρ σ τ} → DTm (σ ⇒ τ) → DTm (ρ ⇒ σ) → DTm (ρ ⇒ τ)
  _<⊙_ : ∀ {ρ σ τ} → DTm (ρ ⇒ σ) → DTm (σ ⇒ τ) → DTm (ρ ⇒ τ)

stage1 : ∀ {Γ σ} → DTm σ → Tm Γ σ
stage1 (` x) = ` x
stage1 (f > x) = stage1 f ∙ stage1 x
stage1 (x < f) = stage1 f ∙ stage1 x
stage1 (f ⊙> g) = ƛ (stage1 f ∙ (stage1 g ∙ (var vz)))
stage1 (g <⊙ f) = ƛ (stage1 f ∙ (stage1 g ∙ (var vz)))
