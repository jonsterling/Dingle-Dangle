module Types (T : Set) where

infixr 8 _⇒_
data Ty : Set where
  ⟨_⟩ : T → Ty
  _⇒_ : Ty → Ty → Ty
