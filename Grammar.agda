module Grammar where

open import STLC
open import Semantics
open import Syntax

mutual
  record Grammar : Set₁ where
    field
      Categories : Set
      Lexicon : Ty Categories → Set
      Semantics : Ty Kinds → Set
      ⟦_⟧-cat : Categories → Ty Kinds
      ⟦_⟧-lex : ∀ {σ} → Lexicon σ → SemCalculus.Tm Semantics (denote ⟦_⟧-cat σ)

  denote : ∀ {Cat : Set} → (Cat → Ty Kinds) → Ty Cat → Ty Kinds
  denote ck ⟨ x ⟩ = ck x
  denote ck (σ ⇒ τ) = denote ck σ ⇒ denote ck τ


module Interpretation (g : Grammar) where
  open Grammar g
  open Lambda

  ⟦_⟧* : Ty Categories → Ty Kinds
  ⟦_⟧* = denote ⟦_⟧-cat
  
  ⟦_⟧ : ∀ {σ} → SynCalculus.Closed Categories Lexicon σ → SemCalculus.Tm Semantics ⟦ σ ⟧*
  ⟦ ` x ⟧ = ⟦ x ⟧-lex
  ⟦ e ∙ e₁ ⟧ = ⟦ e ⟧ ∙ ⟦ e₁ ⟧

open Interpretation {{...}} public

