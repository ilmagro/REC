## Summary
The goal of this repository is to formalize **REC** language
(*"The Formal Semantics of Programming Languages"*, **Winksel**).
The formalization is general for both `Var` (which equality must be decidable) and `FVar`.
Furthermore, the formalization is cubical-compatible but still requires to suppress
`UnsupportedIndexedMatch` warning.

The most notable results are a
[**call-by-value (big-step) operational semantics**](Base.agda#L56-L76)
and its relative proof of [**determinism**](Base.agda#L78-L95).

## Requirements
- **Agda**

Note: agda-stdlib is not required.

## TODO
- subsitution lemmas
- small-step operational semantics
- denotational semantics
- call-by-name semantic variants
