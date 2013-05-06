module Kit.Either where

data _+_ (S T : Set) : Set where
  inl : S → S + T
  inr : T → S + T
