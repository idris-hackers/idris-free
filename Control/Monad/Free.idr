module Control.Monad.Free

%default total

data Free : (f : Type -> Type) -> (a : Type) -> Type where
  Pure : a -> Free f a
  Bind : f (Free f a) -> Free f a

instance Functor f => Functor (Free f) where
  map f (Pure x) = Pure (f x)
  map f (Bind x) = assert_total (Bind (map (map f) x))

instance Functor f => Applicative (Free f) where
  pure = Pure

  (Pure f) <*> x = map f x
  (Bind f) <*> x = assert_total (Bind (map (<*> x) f))

instance Functor f => Monad (Free f) where
  (Pure x) >>= f = f x
  (Bind x) >>= f = assert_total (Bind (map (>>= f) x))

liftFree : Functor f => f a -> Free f a
liftFree = Bind . map Pure

lowerFree : Monad f => Free f a -> f a
lowerFree (Pure x) = return x
lowerFree (Bind f) = assert_total (flatten (map lowerFree f))

iterM : (Monad m, Functor f) => (f (m a) -> m a) -> Free f a -> m a
iterM f (Pure x) = return x
iterM f (Bind x) = assert_total (f (map (iterM f) x))

class MonadFree (m : Type -> Type) (f : Type -> Type) | m where
  wrap : f (m a) -> m a

instance MonadFree (Free f) f where
  wrap = Bind
