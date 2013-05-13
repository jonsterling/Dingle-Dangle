{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE RankNTypes #-}

module Syntax where

infixr :~>
data Ty cat :: * where
  C     :: cat -> Ty cat
  (:~>) :: Ty cat -> Ty cat -> Ty cat

data Expr (lex :: Ty cat -> *) :: Ty cat -> * where
  L    :: Show (lex t) => lex t -> Expr lex t
  (:|>) :: Expr lex (s :~> t) -> Expr lex s -> Expr lex t
  (:<|) :: Expr lex s -> Expr lex (s :~> t) -> Expr lex t
  (:.>) :: Expr lex (s :~> t) -> Expr lex (r :~> s) -> Expr lex (r :~> t)
  (:<.) :: Expr lex (r :~> s) -> Expr lex (s :~> t) -> Expr lex (r :~> t)

infixl 9 :@
data Term (lex :: Ty cat -> *) (v :: Ty cat -> *) :: Ty cat -> * where
  Lex  :: lex s -> Term lex v s
  Var  :: v s -> Term lex v s
  Lam  :: (v s -> Term lex v t) -> Term lex v (s :~> t)
  (:@) :: Term lex v (s :~> t) -> Term lex v s -> Term lex v t

data Norm (lex :: Ty cat -> *) (v :: Ty cat -> *) :: Ty cat -> * where
  NZ :: v t -> Norm lex v t
  NS :: Term lex (Norm lex v) t -> Norm lex v t

norm :: Term lex (Norm lex v) t -> Term lex (Norm lex v) t
norm (Lex l)      = Lex l
norm (Var (NZ v)) = Var (NZ v)
norm (Var (NS t)) = norm t
norm (f :@ x)     =
  case norm f of
    Var (NS f') -> norm (f' :@ x)
    Lam e       -> norm (e (NS x))
    f'          -> f' :@ norm x
norm (Lam e)      = Lam (\v -> norm (e v))

cut :: Term lex (Norm lex v) t -> Term lex v t
cut (Lex l)      = Lex l
cut (Var (NZ v)) = Var v
cut (Var (NS t)) = cut t
cut (f :@ x)     = (cut f) :@ (cut x)
cut (Lam e)      = Lam (\v -> cut (e (NZ v)))

normalize :: (forall v. Term lex v t) -> Term lex v t
normalize t = cut (norm t)

data Cat = N | D | V | P
data Lex :: Ty Cat -> * where
  Eis         :: Lex (C D :~> C P)
  Tosouton    :: Lex (C N :~> C D)
  Eleutherias :: Lex (C N)
  Hkomen      :: Lex (C P :~> C V)
deriving instance Show (Lex t)

instance Show (Expr Lex t) where
  show (L l) = show l
  show (f :|> x)  = show f ++ " |> " ++ show x
  show (x :<| f)  = show x ++ " <| " ++ show f
  show (f :.> g) = show f ++ " .> " ++ show g
  show (f :<. g) = show f ++ " <. " ++ show g

instance Show (Term Lex v t) where
  show (Lex l)  = show l
  show (f :@ x) = show f ++ " :@ " ++ show x
  show (Lam x)  = "Lam"
  show (Var x)  = "Var"

conv :: Expr lex t -> Term lex v t
conv (L x) = Lex x
conv (f :|> x) = (conv f) :@ (conv x)
conv (x :<| f) = (conv f) :@ (conv x)
conv (f :.> g) = Lam (\x -> (conv f) :@ (conv g :@ Var x))
conv (g :<. f) = Lam (\x -> (conv f) :@ (conv g :@ Var x))

eval :: Expr lex t -> Term lex v t
eval t = normalize $ conv t

class Merge (s :: Ty cat) (t :: Ty cat) (r :: Ty cat) | s t -> r where
  (<>) :: Expr lex s -> Expr lex t -> Expr lex r
instance Merge (C x :~> y) (C x) y where
  (<>) = (:|>)
instance Merge (C x) (C x :~> y) y where
  (<>) = (:<|)
instance Merge (x :~> y) (y :~> z) (x :~> z) where
  (<>) = (:<.)
instance Merge (y :~> z) (x :~> y) (x :~> z) where
  (<>) = (:.>)

explicit  = L Eis :.> L Tosouton :<. L Hkomen :|> L Eleutherias
inferred  = L Eis <> L Tosouton <> L Hkomen <> L Eleutherias

