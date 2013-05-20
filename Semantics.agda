module Semantics where

open import Calculus

data Kinds : Set where
  E T : Kinds

data Axiom (W : Ty Kinds → Set) : Ty Kinds → Set where
  iota : Axiom W ((⟨ E ⟩ ⇒ ⟨ T ⟩) ⇒ ⟨ E ⟩)
  and : Axiom W (⟨ T ⟩ ⇒ ⟨ T ⟩ ⇒ ⟨ T ⟩)
  w : ∀ {σ} → W σ → Axiom W σ

pred : Ty Kinds
pred = ⟨ E ⟩ ⇒ ⟨ T ⟩

module SemCalculus W where
  open Lambda Kinds (Axiom W) public

  _∧_ : ∀ {V} → Term V ⟨ T ⟩ → Term V ⟨ T ⟩ → Term V ⟨ T ⟩
  x ∧ y = ` and ∙ x ∙ y

  `ι : ∀ {V} → (V ⟨ E ⟩ → Term V ⟨ T ⟩) → Term V ⟨ E ⟩
  `ι z = ` iota ∙ lam z

  syntax `ι (λ x → B) = ι x ⇒ B

