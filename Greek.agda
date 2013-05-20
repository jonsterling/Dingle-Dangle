module Greek where

open import Calculus
open import Semantics
open import Kit.Equality
open import Kit.Empty


module GreekGrammar where
  open Semantics
  open import Grammar public

  open Lambda
  
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

  ⟦_⟧l : ∀ {σ} → Lex σ → SemCalculus.Tm Sem (denote ⟦_⟧c σ)
  ⟦ τὴν       ⟧l = ` iota
  ⟦ εὐρυτείαν ⟧l = ƛ x ⇒ ƛ y ⇒ ` and ∙ (var x ∙ var y) ∙ (` w ⟦εὐρυτείαν⟧ ∙ var y)
  ⟦ παρθένον  ⟧l = ` w ⟦παρθένον⟧
  ⟦ οἶσθα     ⟧l = ` w ⟦οἶσθα⟧
  ⟦ δῆτα      ⟧l = ƛ x ⇒ var x
  
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
    test-syntax : ⟦ interpret sentence ⟧≅ (` δῆτα ∙ (` οἶσθα ∙ (` τὴν ∙ (` εὐρυτείαν ∙ ` παρθένον))))
    test-syntax = refl

    ex-closed-form : Closed ⟨ V ⟩
    ex-closed-form = closed {λ _ → ⊥} (normalize (interpret sentence))

  module TestSemantics where
    open SemCalculus Sem
    open TestSyntax using (ex-closed-form)

    -- We can interpret the syntactic representation into Logical Form:
    --
    --    ⟦οἶσθα⟧(ιz. ⟦παρθένον⟧(z) ∧ ⟦εὐρυτείαν⟧(z))
    
    test-semantics : ⟦ ⟦ ex-closed-form ⟧ ⟧≅ (` w ⟦οἶσθα⟧ ∙ (ι z ⇒ (` w ⟦παρθένον⟧ ∙ var z) ∧ (` w ⟦εὐρυτείαν⟧ ∙ var z)))
    test-semantics = refl

