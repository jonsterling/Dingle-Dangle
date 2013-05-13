module Syntax

-- Given a set of syntactic categories, we can construct
-- a simple type system.
using (Cat : Type) {

  infixr 70 ~>

  data Ty : Type where
    C : Cat -> Ty
    (~>) : Ty -> Ty-> Ty

  implicit catToTy : Cat -> Ty
  catToTy = C

  -- Given a lexicon, we can construct a syntax.
  using (Lex : Ty -> Type) {

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


    data Term : (Ty -> Type) -> Ty -> Type where
      L'    : Lex t -> Term v t
      V   : {v : Ty -> Type} -> v t -> Term v t
      Lam   : {v : Ty -> Type} -> (v s -> Term v t) -> Term v (s ~> t)
      (<$>) : Term v (s ~> t) -> Term v s -> Term v t

    data Var : (Ty -> Type) -> Ty -> Type where
      VZ : {v : Ty -> Type} -> v t -> Var v t
      VS : {v : Ty -> Type} -> Term (Var v) t -> Var v t

    norm : Term (Var v) t -> Term (Var v) t
    norm (L' l)     = L' l
    norm (V (VZ v)) = V (VZ v)
    norm (V (VS t)) = norm t
    norm (f <$> x)  =
      case norm f of
        V (VS f') => norm (f' <$> x)
        Lam e     => norm (e (VS x))
        f'        => f' <$> norm x
    norm (Lam e)    = Lam (\v => norm (e v))

    cut : Term (Var v) t -> Term v t
    cut (L' l)     = L' l
    cut (V (VZ v)) = V v
    cut (V (VS t)) = cut t
    cut (f <$> x)  = (cut f) <$> (cut x)
    cut (Lam e)    = Lam (\v => cut (e (VZ v)))

    convert : Expr t -> Term v t
    convert (L x) = L' x
    convert (f |> x) = convert f <$> convert x
    convert (x <| f) = convert f <$> convert x
    convert (f .> g) = Lam (\v => convert f <$> (convert g <$> (V v)))
    convert (g <. f) = Lam (\v => convert f <$> (convert g <$> (V v)))

    normalize : ((v : Ty -> Type) -> Term v t) -> Term v t
    normalize t = (cut (norm (t _)))

    Tm : Ty -> Type
    Tm = Term (const ())

    eval : Expr t -> Tm t
    eval e = normalize (\_ => convert e)

    implicit lexToExpr : Lex t -> Expr t
    lexToExpr = L
  }
}


