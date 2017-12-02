module Data.Functor.Coyoneda

%access public export

data Coyoneda : (f : Type -> Type) -> (a : Type) -> Type where
  Coyo : {b : Type} -> (b -> a) -> f b -> Coyoneda f a

Functor (Coyoneda f) where
  map f (Coyo h c) = Coyo (f . h) c

liftCoyoneda : f a -> Coyoneda f a
liftCoyoneda f = Coyo id f

lowerCoyoneda : Functor f => Coyoneda f a -> f a
lowerCoyoneda (Coyo f c) = map f c
