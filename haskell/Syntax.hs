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
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Syntax where

import GHC.TypeLits
import TypeCast

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
  Thn         :: Lex (C N :~> C D)
  Euryteian   :: Lex (C N :~> C N)
  Oistha      :: Lex (C D :~> C V)
  Dhta        :: Lex (C V :~> C V)
  Parthenon   :: Lex (C N)
  Pedas       :: Lex (C N)
  DNull       :: Lex (C N :~> C D)
  Ebale       :: Lex (C D :~> C V)
  Xryseias    :: Lex (C N :~> C N)
  Ekeinon     :: Lex (C D :~> C D)
  Eidon       :: Lex (C D :~> C V)
  Ton         :: Lex (C N :~> C D)
  Andra       :: Lex (C N)
  Naumaxia    :: Lex (C N)
  Gignetai    :: Lex (C D :~> C V)
  Ep'         :: Lex (C D :~> C P)
  APPL        :: Lex (C P :~> C V :~> C V)
  Aiginhi     :: Lex (C N)
  Megalh      :: Lex (C N :~> C N)


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

class Merge s t (r :: *) | s t -> r where
  (<>) :: s -> t -> r

data Empty
class Merge' (flag :: Bool) s t r | flag s t -> r where
  merge' :: Sing flag -> s -> t -> r

data instance Sing (a :: Bool) where
  SFalse :: Sing False
  STrue :: Sing True
instance SingI True where sing = STrue
instance SingI False where sing = SFalse

class MergePred a b (flag :: Bool) | a b -> flag
instance TypeCast flag False => MergePred a b flag
instance MergePred (Expr lex (C x :~> y)) (Expr lex (C x)) True
instance MergePred (Expr lex (C x)) (Expr lex (C x :~> y)) True
instance MergePred (Expr lex (x :~> y)) (Expr lex (y :~> z)) True
instance MergePred (Expr lex (y :~> z)) (Expr lex (x :~> y)) True

instance Merge' True (Expr lex (C x :~> y)) (Expr lex (C x)) (Expr lex y) where
  merge' _ = (:|>)
instance Merge' True (Expr lex (C x)) (Expr lex (C x :~> y)) (Expr lex y) where
  merge' _ = (:<|)
instance Merge' True (Expr lex (x :~> y)) (Expr lex (y :~> z)) (Expr lex (x :~> z)) where
  merge' _ = (:<.)
instance Merge' True (Expr lex (y :~> z)) (Expr lex (x :~> y)) (Expr lex (x :~> z)) where
  merge' _  = (:.>)
instance Merge' False s t () where
  merge' _ _ _ = ()
  
instance (SingI flag, MergePred s t flag, Merge' flag s t r) => Merge s t r where
  (<>) = merge' (sing :: Sing flag)

test1 = L Eis <> L Tosouton
test2 = L Thn <> L Euryteian <> L Oistha <> L Dhta <> L Parthenon
test3 = L Pedas <> (L Ebale <> L DNull <> L Xryseias)
test4 = L Ekeinon <> L Eidon <> L Ton <> L Andra
test5 = L Naumaxia <> (L Gignetai <> (L APPL <> L Ep' <> L DNull <> L Aiginhi) <> L DNull <> L Megalh)
