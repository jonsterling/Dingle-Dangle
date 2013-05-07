module Grammar where

open import Calculus
open import Semantics
open import Syntax

mutual
  record Grammar : Set₁ where
    field
      Categories : Set
      Lexicon : Ty Categories → Set
      Semantics : Ty Kinds → Set
      ⟦_⟧-cat : Categories → Ty Kinds
      ⟦_⟧-lex : ∀ {σ} → Lexicon σ → SemCalculus.Tm Semantics ε (denote ⟦_⟧-cat σ)

  denote : ∀ {Cat : Set} → (Cat → Ty Kinds) → Ty Cat → Ty Kinds
  denote ck ⟨ x ⟩ = ck x
  denote ck (σ ⇒ τ) = denote ck σ ⇒ denote ck τ

open Grammar {{...}} public
open Lambda

⟦_⟧* : ∀ {{g : Grammar}} → Ty Categories → Ty Kinds
⟦_⟧* = denote ⟦_⟧-cat

⟦_⟧ : ∀ {{g : Grammar}} {σ} → SynCalculus.CTm Categories Lexicon σ → SemCalculus.Tm Semantics ε ⟦ σ ⟧*
⟦_⟧ {{g}} (` x) = ⟦ x ⟧-lex
⟦_⟧ {{g}} (f ∙ x) = ⟦ f ⟧ ∙ ⟦ x ⟧
