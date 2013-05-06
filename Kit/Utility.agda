module Kit.Utility where

_∘_ : {A : Set}{B : A → Set}{C : (a : A) → B a → Set} →
     (∀ {a} b → C a b) → (g : (∀ (a : A) → B a)) → ∀ (a : A) → C a (g a)
f ∘ g = λ a → f (g a)

id : {A : Set} → A → A
id a = a
