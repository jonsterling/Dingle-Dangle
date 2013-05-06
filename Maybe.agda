module Maybe where

data Maybe (A : Set) : Set where
  just    : A → Maybe A
  nothing : Maybe A

