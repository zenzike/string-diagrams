{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TupleSections #-}

{- TODO:

   - Enhance End so it has Funct, Uniq, and two Ints (e.g. 7 of 9)
   - Modify wire to capture that info
   - Change match to compute angles based on 7 of 9 info
   - Add a (Maybe Diagram) to NT
   - other fun things!

-}

module Main where

import           Control.Applicative
import           Control.Arrow
import           Control.Comonad.Cofree
import           Control.Monad.Supply
import           Data.Function
import           Data.Maybe
import           Data.Traversable
import           Diagrams.Backend.SVG.CmdLine
import           Diagrams.Prelude
import           Diagrams.TwoD.Path.Metafont
import           Prelude                      hiding (mapM)

type Term = Cofree TermF
type Uniq = Int

data TermF x
  = Atom NT Uniq
  | Horz [x]
  | Vert [x]
  deriving (Functor, Show)

traverse' :: Applicative m => (Uniq -> m Uniq) -> Term a -> m (Term a)
traverse' f (a :< Atom n u) = ((a :<) . Atom n) <$> f u
traverse' f (a :< Horz xs)  = ((a :<) . Horz) <$> traverse (traverse' f) xs
traverse' f (a :< Vert xs)  = ((a :<) . Vert) <$> traverse (traverse' f) xs

data NT = NT String Type
        | Id Funct
        deriving Show

nt :: String -> Type -> Term ()
nt n t = () :< Atom (NT n t) 0

i :: Funct -> Term ()
i f = () :< Atom (Id f) 0

horz :: [Term ()] -> Term ()
horz ts = () :< Horz ts

vert :: [Term ()] -> Term ()
vert ts = () :< Vert ts

type Funct = Maybe String

r = Just "R"
l = Just "L"

ε = nt "epsilon" ([ r , l ], [Nothing])
η = nt "eta"     ([Nothing], [l, r])

epsilon = ε
eta = η

ex1 :: Term ()
ex1 = vert [ horz [ ε, i r ], horz [ i r, η ]]

deco :: Term a -> (a, Term a)
deco (a :< f) = (a, a :< f)

type Joint = (Uniq, Angle)
type Edge = (Joint, Joint)

type Type = ([Funct], [Funct])
type End = (Funct, Uniq)
type IFace = ([End], [End])
type IVert = ((IFace, [Term IFace]), [Edge])

uniq :: Term a -> Term a
uniq t = evalSupply (traverse' (const supply) t) [(0 :: Int) ..]

wire :: Term () -> Maybe (Term IFace, [Edge])
wire (() :< (Atom (NT n (is, os)) u)) = Just ((map (, u) is, map (, u) os) :< (Atom (NT n (is, os)) u), [])
wire (() :< (Atom (Id f) u))          = Just (([(f, u)], [(f, u)]) :< (Atom (Id f) u), [])
wire (() :< (Horz xs ))               =
  case mapM wire xs of
    Nothing -> Nothing
    Just ts -> Just . ((uncurry (:<) . (((concat *** concat) . unzip) *** Horz) . unzip . map deco) *** concat) . unzip $ ts
wire (() :< (Vert xs))           =
  case mapM wire xs of
    Nothing -> Nothing
    Just [] -> Nothing
    Just ts -> fmap ((uncurry (:<) . second Vert) *** id) . foldr1 op $ (map (strength . first adorn) ts)
  where
    op :: Maybe IVert -> Maybe IVert -> Maybe IVert
    op Nothing _ = Nothing
    op _ Nothing = Nothing
    op (Just (((is,os), ts), es)) (Just (((is',os'), ts'), es'))
      = case match os' is of
          Nothing   -> Nothing
          Just es'' -> Just (((is, os'), ts ++ ts'), es ++ es' ++ es'')

strength :: Functor m => (m a, b) -> m (a, b)
strength (m, b) = (, b) <$> m

match :: [End] -> [End] -> Maybe [Edge]
match ((Nothing, _):xs) ys = match xs ys
match xs ((Nothing, _):ys) = match xs ys
match [] [] = Just []
match [] _  = Nothing
match _ []  = Nothing
match ((Just x, i):xs) ((Just y, j):ys)
  | x == y     = (((i, 270@@deg),(j, 270@@deg)) :) <$> match xs ys
  | otherwise  = Nothing

adorn :: Term IFace -> Maybe (IFace, [Term IFace])
adorn t@(a :< _) = Just (a, [t])

drawTerm :: Term IFace -> [Edge] -> Diagram B R2
drawTerm t es = drawBlocks t # drawEdges es

drawBlocks :: Term IFace -> Diagram B R2
drawBlocks (_ :< Atom _ u) = square 1 # named u
drawBlocks (_ :< Horz xs)  = map drawBlocks xs # hcat # centerX
drawBlocks (_ :< Vert xs)  = map drawBlocks xs # reverse # vcat # centerY

drawEdges :: [Edge] -> Diagram B R2 -> Diagram B R2
drawEdges = applyAll . map drawEdge
  where
    drawEdge ((u1,a1),(u2,a2)) =
      withNames [u1, u2] $ \[sub1, sub2] ->
        atop (metafont $ location sub1 .- leaving (fromDirection a1) <> arriving (fromDirection a2) -. endpt (location sub2))

main = case wire (uniq ex1) of
         Nothing -> return ()
         Just (t, es) -> defaultMain (drawTerm t es)
