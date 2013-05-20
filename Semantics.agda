module Semantics where

import STLC
import Types

data Kinds : Set where
  E T : Kinds

module SemanticsAxioms where
  open Types
  
  data Axiom (W : Ty Kinds → Set) : Ty Kinds → Set where
    iota : Axiom W ((⟨ E ⟩ ⇒ ⟨ T ⟩) ⇒ ⟨ E ⟩)
    and : Axiom W (⟨ T ⟩ ⇒ ⟨ T ⟩ ⇒ ⟨ T ⟩)
    w : ∀ {σ} → W σ → Axiom W σ
  
  pred : Ty Kinds
  pred = ⟨ E ⟩ ⇒ ⟨ T ⟩

module SemCalculus W where
  open SemanticsAxioms public
  open STLC Kinds (Axiom W) public

  _∧_ : ∀ {V} → Term V ⟨ T ⟩ → Term V ⟨ T ⟩ → Term V ⟨ T ⟩
  x ∧ y = ` and ∙ x ∙ y

  `ι : ∀ {V} → (V ⟨ E ⟩ → Term V ⟨ T ⟩) → Term V ⟨ E ⟩
  `ι z = ` iota ∙ lam z

  syntax `ι (λ x → B) = ι x ⇒ B

