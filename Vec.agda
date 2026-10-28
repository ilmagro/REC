{-# OPTIONS --safe --cubical-compatible #-}

open import Agda.Builtin.Nat renaming (Nat to ℕ)

module Vec where

data Vec {𝑎} (A : Set 𝑎) : ℕ → Set 𝑎 where
  []  : Vec A zero
  _∷_ : ∀ {n} (x : A) (xs : Vec A n) → Vec A (suc n)

map : ∀ {𝑎 𝑏} {A : Set 𝑎} {B : Set 𝑏} {n} → (A → B) → Vec A n → Vec B n
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs
