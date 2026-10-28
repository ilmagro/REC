{-# OPTIONS --safe --cubical-compatible #-}

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Decidability
open import Equality
open import Vec

module Example where

data Var : Set where
    x y : Var

_≟ᵥ_ : (v₁ v₂ : Var) → Dec (v₁ ≡ v₂)
x ≟ᵥ x = yes refl
x ≟ᵥ y = no λ ()
y ≟ᵥ x = no λ ()
y ≟ᵥ y = yes refl

data FVar : Set where
  f₁ : FVar

arity : FVar → ℕ
arity f₁ = 1

open import Base Var FVar arity _≟ᵥ_

f₁-body : Term
f₁-body = f₁ ∙ ((TVar x +ᵀ (TConst 1)) ∷ [])

f₁-decl : Decl (arity f₁)
f₁-decl = decl (x ∷ []) f₁-body
