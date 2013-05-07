module Greek where

open import Calculus
open import Semantics
open import Kit.Equality


module GreekGrammar where
  open Semantics
  open import Grammar public

  open Lambda using (ƛ; _∙_; var; `_)
  
  data Cat : Set where
    N D V P : Cat
  
  data Lex : Ty Cat → Set where
    τὴν        : Lex (⟨ N ⟩ ⇒ ⟨ D ⟩)
    εὐρυτείαν  : Lex (⟨ N ⟩ ⇒ ⟨ N ⟩)
    παρθένον   : Lex ⟨ N ⟩
    οἶσθα      : Lex (⟨ D ⟩ ⇒ ⟨ V ⟩)
    δῆτα       : Lex (⟨ V ⟩ ⇒ ⟨ V ⟩)
  
  open import Syntax Cat Lex public
  
  data Sem : Ty Kinds → Set where
    ⟦εὐρυτείαν⟧ : Sem pred
    ⟦παρθένον⟧  : Sem pred
    ⟦οἶσθα⟧     : Sem pred
  ⟦_⟧c : Cat → Ty Kinds
  ⟦ N ⟧c = pred
  ⟦ D ⟧c = ⟨ E ⟩
  ⟦ V ⟧c = ⟨ T ⟩
  ⟦ P ⟧c = pred

  ⟦_⟧l : ∀ {σ} → Lex σ → SemCalculus.Tm Sem ε (denote ⟦_⟧c σ)
  ⟦ τὴν       ⟧l = ` ι
  ⟦ εὐρυτείαν ⟧l = ƛ (ƛ (` ∧ ∙ (var (vs vz) ∙ var vz) ∙ (` w ⟦εὐρυτείαν⟧ ∙ var vz)))
  ⟦ παρθένον  ⟧l = ` w ⟦παρθένον⟧
  ⟦ οἶσθα     ⟧l = ` w ⟦οἶσθα⟧
  ⟦ δῆτα      ⟧l = ƛ (var vz)
  
  greek : Grammar
  greek = record {
            Categories = Cat;
            Lexicon = Lex;
            Semantics = Sem;
            ⟦_⟧-cat = ⟦_⟧c;
            ⟦_⟧-lex = ⟦_⟧l }

  
module Examples where
  open GreekGrammar
  -- For the sentence
  --
  --     τὴν εὐρυτείαν οἶσθα δῆτα παρθένον
  --
  -- The following encoding suffices:
  sentence = ` τὴν ⊙> ` εὐρυτείαν <⊙ ` οἶσθα <⊙ ` δῆτα > ` παρθένον


  module TestSyntax where
    open GreekGrammar.SynCalculus

    -- We can normalize our syntactic representation into the following form which favors
    -- locality of logical relations:
    --
    --     δῆτα [ οἶσθα [ τὴν [ εὐρυτείαν [ παρθένον ] ] ] ]
    --
    test-syntax : ⟦ stage1 sentence ⟧≅ (` δῆτα ∙ (` οἶσθα ∙ (` τὴν ∙ (` εὐρυτείαν ∙ ` παρθένον))))
    test-syntax = refl

    ex-closed-form : CTm ⟨ V ⟩
    ex-closed-form = closed' (nm (stage1 sentence) ε)

  module TestSemantics where
    open SemCalculus Sem
    open TestSyntax using (ex-closed-form)

    -- We can interpret the syntactic representation into Logical Form:
    --
    --    ⟦οἶσθα⟧(ιz. ⟦παρθένον⟧(z) ∧ ⟦εὐρυτείαν⟧(z))
    --
    test-semantics : ⟦ ⟦ ex-closed-form ⟧ ⟧≅ (` w ⟦οἶσθα⟧ ∙ (` ι ∙ ƛ (` ∧ ∙ (` w ⟦παρθένον⟧ ∙ var vz) ∙ (` w ⟦εὐρυτείαν⟧ ∙ var vz))))
    test-semantics = refl

