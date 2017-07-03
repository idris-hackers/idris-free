module Control.Monad.Codensity

import Control.Monad.Free

%access public export
%default total

data Codensity : (m : Type -> Type) -> (a : Type) -> Type where
  Codense : ({b : Type} -> (a -> m b) -> m b) -> Codensity m a

runCodensity : Codensity m a -> ({b : Type} -> (a -> m b) -> m b)
runCodensity (Codense c) = c

Functor (Codensity f) where
  map f (Codense c) = Codense (\k => c (k . f))

Applicative (Codensity f) where
  pure x = Codense (\k => k x)
  (Codense f) <*> (Codense x) = Codense (\k => x (\x' => f (\f' => k (f' x'))))

Monad (Codensity f) where
  (Codense x) >>= f = Codense (\k => x (\x' => runCodensity (f x') k))

liftCodensity : Monad m => m a -> Codensity m a
liftCodensity x = Codense (x >>=)

lowerCodensity : Monad m => Codensity m a -> m a
lowerCodensity (Codense c) = c pure

Functor f => MonadFree (Codensity (Free f)) f where
  wrap x = Codense (\k => wrap (map (>>= k) (map lowerCodensity x)))
