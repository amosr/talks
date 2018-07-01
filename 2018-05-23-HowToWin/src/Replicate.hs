module Replicate where

import Prelude hiding (replicate)

replicate :: Int -> a -> [a]
replicate num aa
 | num >  0 = aa : replicate (num - 1) aa
 | otherwise= []


