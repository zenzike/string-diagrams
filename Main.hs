{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}

{- TODO:

   - Why do we need the Id constructor at all?  I think we can get rid
     of it.

   - Enhance NT to contain Angles for each input/output.  Idea is that
     each NT should determine what angles will look best.  Probably we will
     make some smart constructors for making common types: e.g. unit,
     counit, symm, braid, generic m-to-n, etc.  Also makes sense to add a
     (Maybe Diagram) to NT, to be used in the center.

   - Enhance End so it has Funct, Uniq, and Angle

   - Modify wire to save info re: Angles from the NTs into the Ends

   - typecheck categories as well

   - Ah, when typechecking horizontal composition, we also need to
     "pad out" each block vertically so all the blocks have the same height.
     This can be done by simply adding appropriate identity transformations
     (which corresponds to extending strings upwards/downwards).

   - idea: instead of failing with Maybe upon a typechecking error,
     just record the problem in the right place, draw the diagram anyway,
     and *highlight the error* (e.g. a red circle around a place where two
     different functors meet).  In other words, generate *visual* error messages!

   - other fun things!
     - symmetry
     - braiding
     - adjunctions?

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

type Funct = Maybe String

fun :: String -> Funct
fun = Just

type Type = ([(Funct, Angle)], [(Funct, Angle)])

data NT = NT String Type
  deriving Show

nt :: String -> Type -> Term ()
nt n t = () :< Atom (NT n t) 0

i :: Funct -> Term ()
i f = () :< Atom (NT (fromMaybe "" f) ([(f, 270 @@ deg)], [(f, 270 @@ deg)])) 0

id' :: Term ()
id' = () :< Atom (NT "" ([], [])) 0

counit :: String -> Funct -> Funct -> Term ()
counit n f g = nt n ([(f, 0 @@ deg), (g, 180 @@ deg)], [(Nothing, 270 @@ deg)])

unit :: String -> Funct -> Funct -> Term ()
unit n g f = nt n ([(Nothing, 270 @@ deg)], [(g, 180 @@ deg), (f, 0 @@ deg)])

horz :: [Term ()] -> Term ()
horz ts = () :< Horz ts

vert :: [Term ()] -> Term ()
vert ts = () :< Vert ts

infixr 7 ∘
(∘) :: Term () -> Term () -> Term ()
α ∘ β = horz [α, β]

infixr 7 •
(•) :: Term () -> Term () -> Term ()
α • β = vert [α, β]

r, l :: Funct
r = fun "R"
l = fun "L"

ε, epsilon, η, eta :: Term ()
ε = counit "epsilon" r l
η = unit   "eta"     l r

epsilon = ε
eta = η

ex1 :: Term ()
ex1 = (ε ∘ i r) • (i r ∘ η)

deco :: Term a -> (a, Term a)
deco (a :< f) = (a, a :< f)

type Joint = (Uniq, Angle)
type Edge = (Joint, Joint)

type End = ((Funct, Angle), Uniq)
type IFace = ([End], [End])
type IVert = ((IFace, [Term IFace]), [Edge])

uniq :: Term a -> Term a
uniq t = evalSupply (traverse' (const supply) t) [(0 :: Int) ..]

wire :: Term () -> Maybe (Term IFace, [Edge])
wire (() :< (Atom (NT n (is, os)) u)) = Just ((map (, u) is, map (, u) os) :< (Atom (NT n (is, os)) u), [])
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
          Just es'' -> Just (((is', os), ts ++ ts'), es ++ es' ++ es'')

strength :: Functor m => (m a, b) -> m (a, b)
strength (m, b) = (, b) <$> m

match :: [End] -> [End] -> Maybe [Edge]
match (((Nothing, _), _):xs) ys = match xs ys
match xs (((Nothing, _), _):ys) = match xs ys
match [] [] = Just []
match [] _  = Nothing
match _ []  = Nothing
match (((Just x, ax), i):xs) (((Just y, ay), j):ys)
  | x == y     = (((i, ax),(j, ay)) :) <$> match xs ys
  | otherwise  = Nothing

adorn :: Term IFace -> Maybe (IFace, [Term IFace])
adorn t@(a :< _) = Just (a, [t])

drawTerm :: (Renderable (Path R2) b) => Term IFace -> [Edge] -> Diagram b R2
drawTerm t es = drawBlocks t # drawEdges es

drawBlocks :: (Renderable (Path R2) b) => Term IFace  -> Diagram b R2
drawBlocks (_ :< Atom (NT _ (tyi, tyo)) u) = rect (fromIntegral (maximum [1, length tyi, length tyo])) 1 # lw 0 # named u
drawBlocks (_ :< Horz xs)  = map drawBlocks xs # hcat # centerX
drawBlocks (_ :< Vert xs)  = map drawBlocks xs # reverse # vcat # centerY

drawEdges :: (Renderable (Path R2) b) => [Edge] -> Diagram b R2 -> Diagram b R2
drawEdges = applyAll . map drawEdge
  where
    drawEdge ((u1,a1),(u2,a2)) =
      withNames [u1, u2] $ \[sub1, sub2] ->
        atop (metafont $ location sub1 .- leaving (fromDirection a1) <> arriving (fromDirection a2) -. endpt (location sub2))

main = case wire (uniq ex2) of
         Nothing -> return ()
         Just (t, es) -> defaultMain (drawTerm t es)

ex2 = ex1 • (i r ∘ id' ∘ id')

-- main = return ()
