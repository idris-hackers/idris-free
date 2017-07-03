module Control.Monad.Free

%access public export
%default total

data Free : (f : Type -> Type) -> (a : Type) -> Type where
  Pure : a -> Free f a
  Bind : f (Free f a) -> Free f a

Functor f => Functor (Free f) where
  map f m = assert_total $ case m of
    Pure x => Pure (f x)
    Bind x => Bind (map (map f) x)

Functor f => Applicative (Free f) where
  pure = Pure

  m <*> x = assert_total $ case m of
    Pure f => map f x
    Bind f => Bind (map (<*> x) f)

Functor f => Monad (Free f) where
  m >>= f = assert_total $ case m of
    Pure x => f x
    Bind x => Bind (map (>>= f) x)

liftFree : Functor f => f a -> Free f a
liftFree = assert_total $ Bind . map Pure

lowerFree : Monad f => Free f a -> f a
lowerFree m = assert_total $ case m of
  Pure x => pure x
  Bind f => join (map lowerFree f)

iterM : (Monad m, Functor f) => (f (m a) -> m a) -> Free f a -> m a
iterM f m = assert_total $ case m of
  Pure x => pure x
  Bind x => f (map (iterM f) x)

hoistFree : Functor g => ({ a : Type } -> f a -> g a) -> Free f b -> Free g b
hoistFree f m = assert_total $ case m of
  Pure x => Pure x
  Bind x => Bind (hoistFree f <$> f x)

foldFree : (Monad m, Functor f) => ({ a : Type } -> f a -> m a) -> Free f b -> m b
foldFree f m = assert_total $ case m of
  Pure x => pure x
  Bind x => f x >>= foldFree f

interface MonadFree (m : Type -> Type) (f : Type -> Type) | m where
  wrap : f (m a) -> m a

MonadFree (Free f) f where
  wrap = assert_total Bind
