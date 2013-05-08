module Calculus (T : Set) where

open import Kit.Equality
open import Kit.Utility
open import Kit.Empty
open import Kit.Either
open import Kit.Maybe
open import Kit.Bool

import Contexts

infixr 8 _⇒_
data Ty : Set where
  ⟨_⟩ : T → Ty
  _⇒_ : Ty → Ty → Ty

open Contexts Ty public

module Lambda (Axiom : Ty → Set) where
  infixl 8 _∙_

  -- Lambda terms may be axioms, variables, applications and abstractions.
  data Tm (Γ : Con) : Ty → Set where
    `_  : ∀ {σ} → Axiom σ → Tm Γ σ
    var : ∀ {σ} → Var Γ σ → Tm Γ σ
    _∙_ : ∀ {σ τ} → Tm Γ (σ ⇒ τ) → Tm Γ σ → Tm Γ τ
    ƛ   : ∀ {σ τ} → Tm (Γ < σ) τ → Tm Γ (σ ⇒ τ)


  -- Substitutions

  Sub : Con → Con → Set
  Sub Γ Δ = ∀ K {σ} → Var (Γ << K) σ → Tm (Δ << K) σ

  sub : ∀{Γ Δ} → Sub Γ Δ → ∀ K {σ} → Tm (Γ << K) σ → Tm (Δ << K) σ
  sub f K (` x)      = ` x
  sub f K (var x)    = f K x
  sub f K (t ∙ u)    = (sub f K t) ∙ (sub f K u)
  sub f K (ƛ t)      = ƛ (sub f (K < _) t)

  subId : ∀{Γ} → Sub Γ Γ
  subId = λ K x → var x

  subComp : ∀{B Γ Δ} → Sub Γ Δ → Sub B Γ → Sub B Δ
  subComp f g K = sub f K ∘ g K

  -- first monad law, the second holds definitionally
  subid : ∀{Γ}K{σ}(t : Tm (Γ << K) σ) → sub subId K t ≅ id t
  subid K (` x  )    = refl
  subid K (var x)    = refl
  subid K (t ∙ u)    = resp2 Tm._∙_ (subid K t) (subid K u)
  subid K (ƛ t)      = resp ƛ (subid (K < _) t)

  -- third monad law
  subcomp : ∀{B Γ Δ}(f : Sub Γ Δ)(g : Sub B Γ)K{σ}(t : Tm (B << K) σ) →
           sub (subComp f g) K t ≅ (sub f K ∘ sub g K) t
  subcomp f g K (` x)      = refl
  subcomp f g K (var x)    = refl
  subcomp f g K (t ∙ u)    = resp2 Tm._∙_ (subcomp f g K t) (subcomp f g K u)
  subcomp f g K (ƛ t)      = resp ƛ (subcomp f g (K < _) t)


  -- Renaming

  Ren : Con → Con → Set
  Ren Γ Δ = ∀ K {σ} → Var (Γ << K) σ → Var (Δ << K) σ

  renId : ∀{Γ} → Ren Γ Γ
  renId = \ _ x → x

  renComp : ∀{B Γ Δ} → Ren Γ Δ → Ren B Γ → Ren B Δ
  renComp f g = \ K → f K ∘ g K

  ren : ∀{Γ Δ} → Ren Γ Δ → ∀ K {σ} → Tm (Γ << K) σ → Tm (Δ << K) σ
  ren f K x = sub (λ K → subId K ∘ f K) K x

  renid : ∀{Γ} K {σ}(t : Tm (Γ << K) σ) → ren renId K t ≅ id t
  renid = subid


  rencomp : ∀ {B Γ Δ}(f : Ren Γ Δ)(g : Ren B Γ) K {σ}(t : Tm (B << K) σ) →
             ren (renComp f g) K t ≅ (ren f K ∘ ren g K) t
  rencomp f g K (` x)      = refl
  rencomp f g K (var x)    = refl
  rencomp f g K (t ∙ u)    = resp2 Tm._∙_ (rencomp f g K t) (rencomp f g K u)
  rencomp {B}{Γ}{Δ} f g K (ƛ t) = resp ƛ (rencomp f g (K < _) t)

  -- these are now corollaries
  rensub : ∀{B Γ Δ}(f : Ren Γ Δ)(g : Sub B Γ)K{σ}(t : Tm (B << K) σ) →
          (ren f K ∘ sub g K) t ≅ sub (λ K → ren f K ∘ g K) K t
  rensub f g K t = sym (subcomp (λ K → subId K ∘ f K) g K t)

  subren : ∀{B Γ Δ}(f : Sub Γ Δ)(g : Ren B Γ)K{σ}(t : Tm (B << K) σ) →
          (sub f K ∘ ren g K) t ≅ sub (λ K → f K ∘ g K) K t
  subren f g K x = sym (subcomp f (λ K → subId K ∘ g K) K x)

  data Case (τ : _) (Γ Δ : Con) : Set where
    inj₁ : (∀ K → Var (K << Γ) τ) → Case τ Γ Δ
    inj₂ : Var Δ τ → Case τ Γ Δ

  case : ∀ {τ} Γ {Δ} → Var (Δ << Γ) τ → Case τ Γ Δ
  case ε x = inj₂ x
  case {τ} (Γ < .τ) vz = inj₁ (λ K → vz)
  case (Γ < σ) (vs x) with case Γ x
  case (Γ < σ) (vs x) | inj₁ τ∈Γ = inj₁ λ K → vs (τ∈Γ K)
  case (Γ < σ) (vs x) | inj₂ τ∈Δ = inj₂ τ∈Δ

  _≪_ : ∀ {Δ τ} → Var Δ τ → ∀ Γ → Var (Δ << Γ) τ
  x ≪ ε = x
  x ≪ (Γ < σ) = vs (x ≪ Γ)

  Con-Ren : ∀ Γ {Δ} → Ren Δ (Δ << Γ)
  Con-Ren Γ K x with case K x
  ... | inj₁ τ∈K = τ∈K _
  ... | inj₂ τ∈Δ = (τ∈Δ ≪ Γ) ≪ K

  lift : ∀ {Γ Δ} → (∀ τ → Var Γ τ → Tm Δ τ) → Sub Γ Δ
  lift f K x with case K x
  lift f K x | inj₁ τ∈K = var (τ∈K _)
  lift f K x | inj₂ τ∈Γ = ren (Con-Ren K) ε (f _ τ∈Γ)

  data Nm (Γ : Con) : Ty → Bool → Set where
    ↑_  : ∀ {τ} → Nm Γ τ false → Nm Γ τ true
    ƛ   : ∀ {σ τ} → Nm (Γ < σ) τ true → Nm Γ (σ ⇒ τ) true
    var : ∀{σ} → Var Γ σ → Nm Γ σ false
    _∙_ : ∀{σ τ} → Nm Γ (σ ⇒ τ) false → Nm Γ σ true → Nm Γ τ false
    `_  : ∀{σ} → Axiom σ → Nm Γ σ false

  Ne Nf : Con → Ty → Set
  Nf Γ σ = Nm Γ σ true
  Ne Γ σ = Nm Γ σ false
  
  mutual
    [_] : Ty → Con → Set
    [ T ] Γ = (∀ {Δ} → Ren Γ Δ → Ne Δ T) + (∀ {Δ} → Ren Γ Δ → [ T ]act Δ)

    [_]act : Ty → Con → Set
    [ ⟨ t ⟩ ]act  Γ = ⊥
    [ S ⇒ T ]act Γ = [ S ] Γ → [ T ] Γ

  ren[] : ∀ {Γ Δ} → Ren Γ Δ → ∀ {τ} → [ τ ] Γ → [ τ ] Δ
  ren[] le (inl y) = inl (λ le' → y (renComp le' le))
  ren[] le (inr y) = inr (λ le' → y (renComp le' le))

  mutual
    quo : ∀ {Γ} (τ : Ty) → [ τ ] Γ → Nf Γ τ
    quo ⟨ t ⟩ (inr x) = ⊥-elim (x renId)
    quo ⟨ t ⟩ (inl e) = ↑ (e renId)
    quo (S ⇒ T) f = ƛ (quo T (ren[] (Con-Ren (ε < _)) f $$ (inl (λ le → var (le ε vz)))))

    _$$_ : forall {Γ S T} → [ S ⇒ T ] Γ → [ S ] Γ → [ T ] Γ
    _$$_ {S = S} (inl fn) s = inl λ le → (fn le) ∙ (quo S (ren[] le s))
    _$$_ (inr fa) s = fa renId s

  data Env : Con → Con → Set where
    ε : ∀ {Γ} → Env ε Γ
    _<_ : ∀ {G Γ S} → Env G Γ → [ S ] Γ → Env (G < S) Γ

  renEnv : ∀ {G Γ Δ} → Ren Γ Δ → Env G Γ → Env G Δ
  renEnv le ε = ε
  renEnv le (g < s) = renEnv le g < ren[] le s

  get : ∀ {G Γ T} → Var G T → Env G Γ → [ T ] Γ
  get vz     (g < s) = s
  get (vs x) (g < t) = get x g

  ev : ∀ {G Γ T} → Tm G T → Env G Γ → [ T ] Γ
  ev (` x) g = inl (λ _ → ` x)
  ev (var x) g = get x g
  ev (f ∙ s) g = ev f g $$ ev s g
  ev (ƛ t) g = inr λ le s → ev t (renEnv le g < s)

  nm : ∀ {G Γ τ} → Tm G τ → Env G Γ → Nf Γ τ
  nm t g = quo _ (ev t g)

  nm₀ : ∀ {τ} → Tm ε τ → Nf ε τ
  nm₀ x = nm x ε

  -- Terms in normal form may be embedded back into the original term language.
  mutual
    ⌈_⌉ : ∀ {Γ σ b} → Nm Γ σ b → Tm Γ σ
    ⌈ ↑ x ⌉ = ⌈ x ⌉
    ⌈ ƛ x ⌉ = ƛ ⌈ x ⌉
    ⌈ var x ⌉ = var x
    ⌈ f ∙ x ⌉ = ⌈ f ⌉ ∙ ⌈ x ⌉
    ⌈ ` x ⌉ = ` x
  
  ⟦_⟧≅_ : ∀ {σ} → Tm ε σ → Tm ε σ → Set
  ⟦ t ⟧≅ nt = ⌈ nm₀ t ⌉ ≅ nt

  -- Closed terms do not have variables or abstractions.
  data Closed : Ty → Set where
    `_ : ∀ {σ} → Axiom σ → Closed σ
    _∙_ : ∀ {σ τ} → Closed (σ ⇒ τ) → Closed σ → Closed τ

  closed? : ∀ {Γ σ b} → Nm Γ σ b → Maybe (Closed σ)
  closed? (↑ x) = closed? x
  closed? (ƛ x) = nothing
  closed? (var x) = nothing
  closed? (f ∙ x) = _∙_ <$> closed? f ⊛ closed? x
  closed? (` x) = just (` x)

  closed : ∀ {σ} {c : Closed σ} (x : Nf ε σ) {p : closed? x ≅ just c} → Closed σ
  closed {c = c} _ = c

