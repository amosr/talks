Incomplete proof of round-tripping for run-length-encoding using `hs-to-coq`.

The implementation of decoding a run-length encoding uses the `replicate :: Int -> a -> [a]` function.
I found this hard to use in hs-to-coq because, as far as Coq can tell, it is not structurally recursive because the argument is a *signed integer* rather than a *natural number*.

I've included the hs-to-coq generated files Replicate.v, List.v, and RunLengthEncoding.v, though these are generated from the corresponding .hs file.
