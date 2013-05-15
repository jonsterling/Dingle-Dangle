{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PolyKinds #-}

module TypeCast where

class TypeCast   a b   | a -> b, b -> a
class TypeCast'  t a b | t a -> b, t b -> a
class TypeCast'' t a b | t a -> b, t b -> a
instance TypeCast'  () a b => TypeCast a b
instance TypeCast'' t a b => TypeCast' t a b
instance TypeCast'' () a a
