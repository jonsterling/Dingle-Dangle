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

    implicit lexToExpr : Lex s -> Expr s
    lexToExpr l = L l


    -- We use a classy little hack to get the metalanguage to evaluate
    -- our expressions for us. First we reflect our types into the
    -- metalanguage; then, we write a quick little evaluator. Both lexical
    -- entries and syntactic categories are "axioms", and should not evaluate
    -- any further. To make this happen, we can just fail to provide
    -- implementations for the embedding functions |C'| and |L'|.

    C' : Cat -> Type

    denote : Ty -> Type
    denote (C c) = C' c
    denote (s ~> t) = denote s -> denote t

    implicit L' : Lex s -> denote s

    eval : Expr s -> denote s
    eval (L x)    = L' x
    eval (f |> x) = (eval f) (eval x)
    eval (x <| f) = (eval f) (eval x)
    eval (f .> g) = \x => (eval f) ((eval g) x)
    eval (g <. f) = \x => (eval f) ((eval g) x)

    syntax "(|" [e] "|)" = eval e
  }
}

