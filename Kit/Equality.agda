module Kit.Equality where

data _≅_ {A : Set} : {A' : Set} → A → A' → Set where
  refl : {a : A} → a ≅ a

trans : ∀{A A' A''}{a : A}{a' : A'}{a'' : A''} → a ≅ a' → a' ≅ a'' → a ≅ a''
trans refl p = p

sym : ∀{A A'}{a : A}{a' : A'} → a ≅ a' → a' ≅ a
sym refl = refl

resp : ∀{A}{B : A → Set}(f : ∀ a → B a){a a' : A} → a ≅ a' → f a ≅ f a'
resp f refl = refl

resp2 : ∀{A}{B : A → Set}{C : (x : A) → B x → Set}(f : (x : A)(y : B x) → C x y)
          {a a' : A} → a ≅ a' → {b : B a}{b' : B a'} → b ≅ b' → f a b ≅ f a' b'
resp2 f refl refl = refl
