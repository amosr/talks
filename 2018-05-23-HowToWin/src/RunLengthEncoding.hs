module RunLengthEncoding where

import Prelude hiding (replicate)
import Replicate

data Element a = E
  { elementValue :: a
  , elementCount :: Int }

type Encoded a = [Element a]

consEncoded :: Eq a => a -> Encoded a -> Encoded a
consEncoded a es
 = case es of
    [] -> [E a 1]
    (e:es)
     | elementValue e == a
     -> e { elementCount = elementCount e + 1 }
        : es
     | otherwise
     -> (E a 1 : e : es)


encode :: Eq a => [a] -> Encoded a
encode as
 = case as of
    [] -> []
    (a:as') -> consEncoded a (encode as')

decode :: Encoded a -> [a]
decode es
 = case es of
    [] -> []
    (e:es') -> replicate (elementCount e) (elementValue e) ++ decode es'
