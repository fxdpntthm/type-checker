Writing A type checker in Haskell
====

This code tries to capture the essense of `algorithm W` or famously known
as Hindley-Milner (HM) algorithm to infer types for a 
simply typed lambda calculus. It will also use the
same language to implement an `algorithm M` that uses an alternative
way of type checking and is better than algorithm W in terms of its
error message generation and performance as it detects errors before
`algorithm W`


