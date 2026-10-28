{-# OPTIONS --safe --cubical-compatible #-}

module Equality where

open import Agda.Builtin.Equality public

sym : ∀ {𝑎} {A : Set 𝑎} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {𝑎} {A : Set 𝑎} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl p = p

cong : ∀ {𝑎 𝑏} {A : Set 𝑎} {B : Set 𝑏} {x y : A} (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

subst : ∀ {𝑎 𝑝} {A : Set 𝑎} {x y : A} (P : A → Set 𝑝) → x ≡ y → P x → P y
subst P refl p = p

-- equational reasoning

infix 1 begin_
begin_ : ∀ {𝑎} {A : Set 𝑎} {x y : A} → x ≡ y → x ≡ y
begin p = p

infix 5 _∎
_∎ : ∀ {𝑎} {A : Set 𝑎} → (x : A) → x ≡ x
x ∎ = refl

infixr 4 _≡⟨_⟩_
_≡⟨_⟩_ : ∀ {𝑎} {A : Set 𝑎} (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ p ⟩ q = trans p q
