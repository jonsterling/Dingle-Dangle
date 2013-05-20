module Examples.Greek where

open import Greek
open import Types
open import Syntax Cat Lex
open import Semantics
open import Kit.Equality
open import Kit.Utility

-- For the sentence
--
--     τὴν εὐρυτείαν οἶσθα δῆτα παρθένον
--
-- The following encoding suffices:
sentence : DTm ⟨ V ⟩
sentence = ` τὴν ⊙> ` εὐρυτείαν <⊙ ` οἶσθα <⊙ ` δῆτα > ` παρθένον

module TestSyntax where
  open SynCalculus

  -- We can normalize our syntactic representation into the following form which favors
  -- locality of semantic relations:
  --
  --     δῆτα [ οἶσθα [ τὴν [ εὐρυτείαν [ παρθένον ] ] ] ]
  --
  test-syntax : ⟦ interpret sentence ⟧≅ (` δῆτα ∙ (` οἶσθα ∙ (` τὴν ∙ (` εὐρυτείαν ∙ ` παρθένον))))
  test-syntax = refl

  ex-closed-form : Closed ⟨ V ⟩
  ex-closed-form = closed (normalize (interpret sentence))

module TestSemantics where
  open SemCalculus Sem
  open TestSyntax using (ex-closed-form)

  -- We can interpret the normalized syntactic representation into Logical Form:
  --
  --    ⟦οἶσθα⟧(ιz. ⟦παρθένον⟧(z) ∧ ⟦εὐρυτείαν⟧(z))
  
  test-semantics : ⟦ ⟦ ex-closed-form ⟧ ⟧≅ (` w ⟦οἶσθα⟧ ∙ (ι z ⇒ (` w ⟦παρθένον⟧ ∙ var z) ∧ (` w ⟦εὐρυτείαν⟧ ∙ var z)))
  test-semantics = refl

