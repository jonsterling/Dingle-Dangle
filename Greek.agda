module Greek where

open import Calculus
open import Semantics
open import Kit.Equality

data Cat : Set where
  N D V P : Cat

data Lex : Ty Cat → Set where
  τὴν        : Lex (⟨ N ⟩ ⇒ ⟨ D ⟩)
  εὐρυτείαν  : Lex (⟨ N ⟩ ⇒ ⟨ N ⟩)
  παρθένον   : Lex ⟨ N ⟩
  οἶσθα      : Lex (⟨ D ⟩ ⇒ ⟨ V ⟩)
  δῆτα       : Lex (⟨ V ⟩ ⇒ ⟨ V ⟩)

open import Syntax Cat Lex

data Sem : Ty Kinds → Set where
  ⟦εὐρυτείαν⟧ : Sem pred
  ⟦παρθένον⟧  : Sem pred
  ⟦οἶσθα⟧     : Sem pred

module SemCalculus' = SemCalculus Sem

module SemInterp where
  open Lambda

  ⟦_⟧sty : Ty Cat → Ty Kinds
  ⟦ ⟨ N ⟩ ⟧sty = pred
  ⟦ ⟨ D ⟩ ⟧sty = ⟨ E  ⟩
  ⟦ ⟨ V ⟩ ⟧sty = ⟨ T ⟩
  ⟦ ⟨ P ⟩ ⟧sty = pred
  ⟦ σ ⇒ τ ⟧sty = ⟦ σ ⟧sty ⇒ ⟦ τ ⟧sty

  ⟦_⟧ : ∀ {σ} → SynCalculus.CTm σ → SemCalculus'.Tm ε ⟦ σ ⟧sty
  ⟦ ` τὴν ⟧ = ` ι
  ⟦ ` εὐρυτείαν ⟧ = ƛ (ƛ (` ∧ ∙ (var (vs vz) ∙ var vz) ∙ (` w ⟦εὐρυτείαν⟧ ∙ var vz)))
  ⟦ ` παρθένον ⟧ = ` w ⟦παρθένον⟧
  ⟦ ` οἶσθα ⟧ = ` w ⟦οἶσθα⟧
  ⟦ ` δῆτα ⟧ = ƛ (var vz)
  ⟦ f ∙ x ⟧ = ⟦ f ⟧ ∙ ⟦ x ⟧

module Examples where
  -- “τὴν εὐρυτείαν οἶσθα δῆτα παρθένον” ⇒ “δῆτα [ οἶσθα [ τὴν [ εὐρυτείαν [ παρθένον ] ] ] ]”
  sentence = ` τὴν ⊙> ` εὐρυτείαν <⊙ ` οἶσθα <⊙ ` δῆτα > ` παρθένον


  module TestSyntax where
    open SynCalculus

    test-syntax : ⟦ stage1 sentence ⟧≅ ↑ (` δῆτα ∙ ↑ (` οἶσθα ∙ ↑ (` τὴν ∙ ↑ (` εὐρυτείαν ∙ ↑ ` παρθένον))))
    test-syntax = refl

    ex-closed-form : CTm ⟨ V ⟩
    ex-closed-form = closed' (nm (stage1 sentence) ε)

  module TestSemantics where
    open SemInterp
    open SemCalculus'
    
    open TestSyntax using (ex-closed-form)

    test-semantics : ⟦ ⟦ ex-closed-form ⟧ ⟧≅ ↑ (` w ⟦οἶσθα⟧ ∙ ↑ (` ι ∙ ƛ (↑ (` ∧ ∙ ↑ (` w ⟦παρθένον⟧ ∙ ↑ (var vz)) ∙ ↑ (` w ⟦εὐρυτείαν⟧ ∙ ↑ (var vz))))))
    test-semantics = refl

