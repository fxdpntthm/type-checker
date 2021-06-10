Type checker in Haskell
====

This code tries to capture the essense of `algorithm W` or famously known
as Hindley-Milner (HM) algorithm to infer types for a 
polymorphic lambda calculus. It will also use the
same language to implement an `algorithm M` that uses an alternative
way of type checking and is better than algorithm W in terms of its
error message generation and performance as it detects errors "before"
`algorithm W`

Features to be implemented
- [x] algorithm w
- [x] algorithm m
- [ ] experiment with bi-directional type checking
- [x] enrich the stlc with fix point combinator
- [ ] Add richer types such as N-rank polymorphism
