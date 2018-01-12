module Control.Monad.Freer

import Control.Monad.Free
import Control.Monad.Syntax
import Data.CoList

%default total
%access public export

-- ported from https://github.com/robrix/freer-cofreer

data Freer : (f : Type -> Type) -> (a : Type) -> Type where
  Pure : a -> Freer f a
  Bind : f x -> (x -> Freer f a) -> Freer f a

Functor (Freer f) where
  map f (Pure result)     = Pure (f result)
  map f (Bind step yield) = Bind step (\x => map f $ yield x)

Applicative (Freer f) where
  pure = Pure

  (Pure f)            <*> param = map f param
  (Bind action yield) <*> param = Bind action (\x => (yield x) <*> param)

Monad (Freer f) where
  (Pure a)   >>= f = f a
  (Bind r f) >>= g = Bind r (f >=> g)

liftF : f a -> Freer f a
liftF action = action `Bind` Pure

hoistFreer : {f, g : Type -> Type} -> (fg : {a : Type} -> f a -> g a) -> Freer f b -> Freer g b
hoistFreer _  (Pure result)     = Pure result
hoistFreer fg (Bind step yield) = Bind (fg step) (\x => hoistFreer fg $ yield x)

||| Tear down a `Freer` `Monad` using iteration with an explicit continuation.
|||
||| This is analogous to `iter` with a continuation for the interior values, and
||| is therefore suitable for defining interpreters for GADTs/types lacking a
||| `Functor` instance.
iterFreer : (algebra : {x : Type} -> (x -> a) -> f x -> a) -> Freer f a -> a
iterFreer _       (Pure result)          = result
iterFreer algebra (Bind action continue) = algebra (\x => iterFreer algebra $ continue x) action

||| Tear down a `Freer` `Monad` using iteration.
|||
||| This is analogous to `cata` where the `Pure`ed values are placeholders for
||| the result of the computation.
iter : Functor f => (algebra : f a -> a) -> Freer f a -> a
iter algebra = iterFreer (\yield => algebra . map yield)

||| Tear down a `Freer` `Monad` using iteration with an explicit continuation in some `Applicative` context.
|||
||| This is analogous to `iterA` with a continuation for the interior values, and
||| is therefore suitable for defining interpreters for GADTs/types lacking a
||| `Functor` instance.
iterFreerA : Applicative m => (algebra : {x : Type} -> (x -> m a) -> f x -> m a) -> Freer f a -> m a
iterFreerA algebra r = iterFreer algebra (map pure r)

||| Tear down a `Freer` `Monad` using iteration in some `Applicative` context.
|||
||| This is analogous to `cata` where the `Pure` values are placeholders for
||| the result of the computation.
iterA : (Functor f, Applicative m) => (algebra : f (m a) -> m a) -> Freer f a -> m a
iterA algebra = iterFreerA (\yield => algebra . map yield)

||| Run a program to completion by repeated refinement, and return its result.
-- TODO can it be made total? use `Fuel`?
partial
runFreer : (refine : {x : Type} -> f x -> Freer f x) -> Freer f result -> result
runFreer refine = iterFreer (\xa, fx => xa $ runFreer refine $ refine fx)

||| Run a program to completion by repeated refinement in some `Monad`ic
||| context, and return its result.
-- TODO can it be made total? use `Fuel`?
partial
runFreerM : Monad m => (refine : {x : Type} -> f x -> Freer f (m x)) -> Freer f result -> m result
runFreerM {m} refine r = go (map pure r)
  where 
  partial
  go : Freer f (m x) -> m x
  go = iterFreer ((. (go . refine)) . (=<<))

||| Run a single step of a program by refinement, returning `Either` its result
||| or the next step.
stepFreer : (refine : {x : Type} -> f x -> Freer f x) -> Freer f result -> Either result (Freer f result)
stepFreer _      (Pure a)          = Left a
stepFreer refine (Bind step yield) = Right (refine step >>= yield)

||| Run a program to completion by repeated refinement, returning the list of
||| steps up to and including the final result. 
|||
||| The steps are unfolded lazily, making this total and suitable for stepwise
||| evaluation of nonterminating programs.
freerSteps : (refine : {x : Type} -> f x -> Freer f x) -> Freer f result -> CoList (Freer f result)
freerSteps refine r = case stepFreer refine r of
  Left  a    => [Pure a]
  Right step => step :: (freerSteps refine step)

retract : Monad m => Freer m a -> m a
retract = iterFreerA (=<<)

foldFreer : Monad m => ({x : Type} -> f x -> m x) -> Freer f a -> m a
foldFreer f = retract . hoistFreer f

cutoff : Nat -> Freer f a -> Freer f (Either (Freer f a) a)
cutoff  Z     r                = pure (Left r)
cutoff (S n) (Bind step yield) = Bind step (cutoff n . yield)
cutoff  _     r                = Right <$> r

MonadFree (Freer f) f where
  wrap action = action `Bind` id

Foldable f => Foldable (Freer f) where
  foldr ff c (Pure a)   = ff a c
  foldr ff c (Bind r t) = foldr (\x,c1 => foldr ff c1 (t x)) c r
    
Traversable f => Traversable (Freer f) where
  traverse f (Pure a)   = pure <$> f a
  traverse f (Bind r t) = wrap <$> traverse (\a => traverse f (t a)) r
