module Syntax

using (Cat : Type) {
  data Ty : Type where
    C : Cat -> Ty
    Fun : Ty -> Ty-> Ty

  syntax [s] "~>" [t] = Fun s t

  using (Lex : Ty -> Type) {
    implicit catToTy : Cat -> Ty
    catToTy = C

    infixl 70 |>
    infixl 70 <|
    infixl 70 <.
    infixl 70 .>

    data Expr : Ty -> Type where
      L     : Lex t -> Expr t
      (|>)  : Expr (s ~> t) -> Expr s -> Expr t
      (<|)  : Expr s -> Expr (s ~> t) -> Expr t
      (.>)  : Expr (s ~> t) -> Expr (r ~> s) -> Expr (r ~> t)
      (<.)  : Expr (r ~> s) -> Expr (s ~> t) -> Expr (r ~> t)

    implicit lexToExpr : Lex s -> Expr s
    lexToExpr {s} l = L l


    -- We use a classy little hack to get the metalanguage to evaluate
    -- our expressions for us. First we reflect our types into the
    -- metalanguage; then, we write a quick little evaluator. Both lexical
    -- and syntactic categories are "axioms", and should not evaluate any
    -- further. To make this happen, we can just fail to provide
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

