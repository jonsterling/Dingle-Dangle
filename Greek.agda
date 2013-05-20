module Greek where

import STLC
open import Semantics
open import Kit.Equality
open import Kit.Empty

open Semantics
open import Grammar public

open import Types
open SemCalculus hiding (⟦_⟧≅_)

data Cat : Set where
  N D V P : Cat

data Lex : Ty Cat → Set where
  τὴν        : Lex (⟨ N ⟩ ⇒ ⟨ D ⟩)
  εὐρυτείαν  : Lex (⟨ N ⟩ ⇒ ⟨ N ⟩)
  παρθένον   : Lex ⟨ N ⟩
  οἶσθα      : Lex (⟨ D ⟩ ⇒ ⟨ V ⟩)
  δῆτα       : Lex (⟨ V ⟩ ⇒ ⟨ V ⟩)
  
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
