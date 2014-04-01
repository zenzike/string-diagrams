{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE PatternSynonyms #-}

module Main where

import Control.Comonad.Cofree
import Control.Arrow
import Data.Function
import Data.Maybe

type Term = Cofree TermF

data TermF x
  = NT Decl
  | Id Funct
  | Horz [x]
  | Vert [x]
 deriving Functor

nt :: Decl -> Term ()
nt d = () :< NT d

i :: Funct -> Term ()
i f = () :< Id f

horz :: [Term ()] -> Term ()
horz ts = () :< Horz ts

vert :: [Term ()] -> Term ()
vert ts = () :< Vert ts

type Funct = Maybe String

data Decl = Decl String [Funct] [Funct]

type Stmt = ([ Decl ], Term ())

main = undefined

r = Just "R"
l = Just "L"

ε = Decl "epsilon" [ r , l ] [Nothing]
η = Decl "eta"     [Nothing] [l, r]

ex1 :: Term ()
ex1 = vert [ horz [ nt ε, i l ], horz [ i l, nt η ]]

deco :: Term a -> (a, Term a)
deco (a :< f) = (a, a :< f)

type Iface = ([Funct], [Funct])

block :: Term () -> Maybe (Term Iface)
block (() :< (NT (Decl n is os))) = Just ((is, os)   :< (NT (Decl n is os)))
block (() :< (Id f ))             = Just (([f], [f]) :< (Id f))
block (() :< (Horz xs ))          = 
  case mapM block xs of
    Nothing -> Nothing
    Just ts -> Just . uncurry (:<) . (((concat *** concat) . unzip) *** Horz) . unzip . map deco $ ts
block (() :< (Vert xs))           =
  case mapM block xs of
    Nothing -> Nothing
    Just ts -> fmap (uncurry (:<) . second Vert) . foldr op Nothing $ ts
  where
    op :: Term Iface -> Maybe (Iface, [Term Iface]) -> Maybe (Iface, [Term Iface])
    op _ Nothing = Nothing
    op t@((is,os) :< _) (Just ((is',os'), ts)) 
      | match os is' = Just ((is, os'), t : ts)
      | otherwise    = Nothing

match = (==) `on` catMaybes
