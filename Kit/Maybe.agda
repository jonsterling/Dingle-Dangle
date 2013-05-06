module Kit.Maybe where

data Maybe (A : Set) : Set where
  just    : A → Maybe A
  nothing : Maybe A

infixl 50 _⊛_
infixl 50 _<$>_

_⊛_ : ∀ {A B} → Maybe (A → B) → Maybe A → Maybe B
just f ⊛ just x = just (f x)
_      ⊛ _ = nothing

_<$>_ : ∀ {A B} → (A → B) → Maybe A → Maybe B
f <$> x = just f ⊛ x

