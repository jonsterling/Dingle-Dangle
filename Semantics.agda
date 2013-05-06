module Semantics where

open import Calculus

data Kinds : Set where
  E T : Kinds

data Axiom (W : Ty Kinds → Set) : Ty Kinds → Set where
  ι : Axiom W ((⟨ E ⟩ ⇒ ⟨ T ⟩) ⇒ ⟨ E ⟩)
  ∧ : Axiom W (⟨ T ⟩ ⇒ ⟨ T ⟩ ⇒ ⟨ T ⟩)
  w : ∀ {σ} → W σ → Axiom W σ

pred : Ty Kinds
pred = ⟨ E ⟩ ⇒ ⟨ T ⟩

module SemCalculus W = Lambda Kinds (Axiom W)

