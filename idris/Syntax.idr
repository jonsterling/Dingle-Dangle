module Syntax
import Decidable.Equality

infixr 70 ~>

data Cat = N | D | V | P

data Ty : Type where
  C : Cat -> Ty
  (~>) : Ty -> Ty -> Ty

implicit catToTy : Cat -> Ty
catToTy = C

data Lex : Ty -> Type where
  εἰς        : Lex (D ~> P)
  τοσοῦτον   : Lex (N ~> D)
  ἥκομεν     : Lex (P ~> V)
  ἐλευθερίας : Lex (C N)

instance Eq Cat where
  N == N = True
  D == D = True
  V == V = True
  P == P = True
  _ == _ = False

instance Eq Ty where
  (C a)    == (C b)    = a == b
  (a ~> b) == (c ~> d) = a == c && b == d
  _        == _        = False

infixl 70 |>
infixl 70 <|
infixl 70 <.
infixl 70 .>

-- A small categorial syntax.
data Expr : Ty -> Type where
  -- lexical entries are axioms in our system
  L     : Lex t -> Expr t
  -- right application: f |> x
  (|>)  : Expr (s ~> t) -> Expr s -> Expr t
  -- left application: x <| f
  (<|)  : Expr s -> Expr (s ~> t) -> Expr t
  -- right composition: f .> g
  (.>)  : Expr (s ~> t) -> Expr (r ~> s) -> Expr (r ~> t)
  -- left composition: g <. f
  (<.)  : Expr (r ~> s) -> Expr (s ~> t) -> Expr (r ~> t)


infixl 70 #
data Term : (Ty -> Type) -> Ty -> Type where
  L'    : Lex t -> Term v t
  Var   : {v : Ty -> Type} -> v t -> Term v t
  Lam   : {v : Ty -> Type} -> (v s -> Term v t) -> Term v (s ~> t)
  (#) : Term v (s ~> t) -> Term v s -> Term v t

data TVar : (Ty -> Type) -> Ty -> Type where
  VZ : {v : Ty -> Type} -> v t -> TVar v t
  VS : {v : Ty -> Type} -> Term (TVar v) t -> TVar v t

norm : Term (TVar v) t -> Term (TVar v) t
norm (L' l)     = L' l
norm (Var (VZ v)) = Var (VZ v)
norm (Var (VS t)) = norm t
norm (f # x)  =
  case norm f of
    Var (VS f') => norm (f' # x)
    Lam e       => norm (e (VS x))
    f'          => f' # norm x
norm (Lam e)    = Lam (\v => norm (e v))

cut : Term (TVar v) t -> Term v t
cut (L' l)     = L' l
cut (Var (VZ v)) = Var v
cut (Var (VS t)) = cut t
cut (f # x)  = (cut f) # (cut x)
cut (Lam e)    = Lam (\v => cut (e (VZ v)))

convert : Expr t -> Term v t
convert (L x) = L' x
convert (f |> x) = convert f # convert x
convert (x <| f) = convert f # convert x
convert (f .> g) = Lam (\v => convert f # (convert g # (Var v)))
convert (g <. f) = Lam (\v => convert f # (convert g # (Var v)))

normalize : ((v : Ty -> Type) -> Term v t) -> Term v t
normalize t = (cut (norm (t _)))

Tm : Ty -> Type
Tm = Term (const ())

eval : Expr t -> Tm t
eval e = normalize (\_ => convert e)

implicit lexToExpr : Lex t -> Expr t
lexToExpr = L

sentence : Expr (C V)
sentence = εἰς .> τοσοῦτον <. ἥκομεν |> ἐλευθερίας

result : Tm (C V)
result = L' ἥκομεν # (L' εἰς # (L' τοσοῦτον # (L' ἐλευθερίας)))

test : eval sentence = result
test = refl

data Direction = Fw | Bw
using (E : Ty -> Type) {
  data Str : Type where
    Nil  : Str
    (::) : E a -> Str -> Str
}

str : Str
str = [ L εἰς, L τοσοῦτον ]

data Merge : Ty -> Ty -> Type where
  RApp : Merge (s ~> t) s
  LApp : Merge s (s ~> t)
  RComp : Merge (t ~> u) (s ~> t)
  LComp : Merge (s ~> t) (t ~> u)

data Focus : Type where
  lend : (x : Ty) -> (r : Ty) -> Expr x -> Expr r -> Focus
  cent : Expr l -> Expr x -> Expr r -> Focus
  rend : Expr l -> Expr x -> Focus

foc : Focus
foc = lend _ _ (L εἰς) (L τοσοῦτον)

justs : List (Maybe a) -> List a
justs []              = []
justs (Just x :: xs)  = x :: justs xs
justs (Nothing :: xs) = justs xs

{-
merges : (s : Ty) -> (t : Ty) -> Maybe (Merge s t)
merges (s ~> t) x with (decEq s x)
  | Yes p = Nothing
  | No p = Nothing
  -}

--merge : Ty -> Ty -> Maybe (Merge, Ty)
--merge a (b ~> c) =

runFocus : Focus -> Maybe Str
runFocus (lend l x a b) = Just []

--actions : Str
--actions = [ part (L εἰς) RComp , done (L τοσοῦτον) ]



