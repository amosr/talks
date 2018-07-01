module List where

import Prelude hiding (map)

data List a = Nil | Cons a (List a)

map :: (a -> b) -> List a -> List b
map f as
 = case as of
    Nil
      -> Nil
    Cons a as'
      -> Cons (f a) (map f as')

append :: List a -> List a -> List a
append as bs
 = case as of
    Nil
      -> bs
    Cons a as'
      -> Cons a (append as' bs)

