{-# OPTIONS --safe --cubical-compatible #-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

open import Agda.Primitive
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Decidability
open import Equality
open import Logic
open import Vec

module Base {𝑣 𝑓} (Var : Set 𝑣)
                  (FVar : Set 𝑓)
                  (arity : FVar → ℕ)
                  (_≟ᵥ_ : ∀ (v₁ v₂ : Var) → Dec (v₁ ≡ v₂)) where

data Term : Set (𝑣 ⊔ 𝑓) where
  TConst        : ℕ → Term
  TVar          : Var → Term
  _+ᵀ_          : Term → Term → Term
  _*ᵀ_          : Term → Term → Term
  if_then_else_ : Term → Term → Term → Term
  _∙_           : (f : FVar) → Vec Term (arity f) → Term

record Decl (n : ℕ) : Set (𝑣 ⊔ 𝑓) where
  constructor decl
  field
    params : Vec Var n
    body   : Term

open Decl

Decls : Set _
Decls = (f : FVar) → Decl (arity f)

substVar : ∀ {n} → Var → Vec Var n → Vec Term n → Term
substVar v [] [] = TVar v
substVar x (y ∷ vs) (t ∷ ts) with x ≟ᵥ y
... | yes _ = t
... | no  _ = substVar x vs ts

mutual
  substTerm : ∀ {n} → Term → Vec Var n → Vec Term n → Term
  substTerm (TConst n)             vs ts = TConst n
  substTerm (TVar x)               vs ts = substVar x vs ts
  substTerm (t₁ +ᵀ t₂)              vs ts = substTerm t₁ vs ts +ᵀ substTerm t₂ vs ts
  substTerm (t₁ *ᵀ t₂)              vs ts = substTerm t₁ vs ts *ᵀ substTerm t₂ vs ts
  substTerm (if t₀ then t₁ else t₂) vs ts = if (substTerm t₀ vs ts)
                                           then (substTerm t₁ vs ts)
                                           else (substTerm t₂ vs ts)
  substTerm (f ∙ xs)               vs ts = f ∙ substVec xs vs ts

  substVec : ∀ {m n} → Vec Term m → Vec Var n → Vec Term n →  Vec Term m
  substVec []       vs ts = []
  substVec (x ∷ xs) vs ts = substTerm x vs ts ∷ substVec xs vs ts

mutual
  data [_]_→ᵥₐ_ (ds : Decls) : Term → ℕ → Set (𝑣 ⊔ 𝑓) where
    →ᵥₐ-num      : ∀ {n} → [ ds ](TConst n) →ᵥₐ n
    →ᵥₐ-+ᵀ       : ∀ {t₁ t₂ n₁ n₂} → [ ds ] t₁ →ᵥₐ n₁ → [ ds ] t₂ →ᵥₐ n₂ → [ ds ] (t₁ +ᵀ t₂) →ᵥₐ (n₁ + n₂)
    →ᵥₐ-*ᵀ       : ∀ {t₁ t₂ n₁ n₂} → [ ds ] t₁ →ᵥₐ n₁ → [ ds ] t₂ →ᵥₐ n₂ → [ ds ] (t₁ *ᵀ t₂) →ᵥₐ (n₁ * n₂)
    →ᵥₐ-if-true  : ∀ {t₀ t₁ t₂ n₁} → [ ds ] t₀ →ᵥₐ zero →
                                   [ ds ] t₁ →ᵥₐ n₁ →
                                   [ ds ] (if t₀ then t₁ else t₂) →ᵥₐ n₁
    →ᵥₐ-if-false : ∀ {t₀ t₁ t₂ n₀ n₂} → [ ds ] t₀ →ᵥₐ n₀ → [ ds ] t₂ →ᵥₐ n₂ → ¬ (n₀ ≡ zero) →
                                      [ ds ] (if t₀ then t₁ else t₂) →ᵥₐ n₂
    →ᵥₐ-∙        : ∀ {f ts n ns} → EvalVec ds ts ns →
                                  [ ds ] (substTerm (body (ds f))
                                                    (params (ds f))
                                                    (map TConst ns)) →ᵥₐ n →
                                  [ ds ] f ∙ ts →ᵥₐ n

  data EvalVec (ds : Decls) : ∀ {n} → Vec Term n → Vec ℕ n → Set (𝑣 ⊔ 𝑓) where
    eval-[] : EvalVec ds [] []
    eval-∷  : ∀ {t n m ts ns} → [ ds ] t →ᵥₐ n →
                                EvalVec ds {n = m} ts ns →
                                EvalVec ds (t ∷ ts) (n ∷ ns)

mutual
  →ᵥₐ-det : ∀ {ds t n₁ n₂} → [ ds ] t →ᵥₐ n₁ → [ ds ] t →ᵥₐ n₂ → n₁ ≡ n₂
  →ᵥₐ-det →ᵥₐ-num              →ᵥₐ-num              = refl
  →ᵥₐ-det (→ᵥₐ-+ᵀ p₁ p₂)        (→ᵥₐ-+ᵀ q₁ q₂)        = trans (cong _ (→ᵥₐ-det p₁ q₁))
                                                           (cong _ (→ᵥₐ-det p₂ q₂))
  →ᵥₐ-det (→ᵥₐ-*ᵀ p₁ p₂)        (→ᵥₐ-*ᵀ q₁ q₂)        = trans (cong _ (→ᵥₐ-det p₁ q₁))
                                                           (cong _ (→ᵥₐ-det p₂ q₂))
  →ᵥₐ-det (→ᵥₐ-if-true _ p)    (→ᵥₐ-if-true _ q)    = →ᵥₐ-det p q
  →ᵥₐ-det (→ᵥₐ-if-true p _)    (→ᵥₐ-if-false q _ r) = ⊥-elim (r (→ᵥₐ-det q p))
  →ᵥₐ-det (→ᵥₐ-if-false p _ r) (→ᵥₐ-if-true q _)    = ⊥-elim (r (→ᵥₐ-det p q))
  →ᵥₐ-det (→ᵥₐ-if-false _ p _) (→ᵥₐ-if-false _ q _) = →ᵥₐ-det p q
  →ᵥₐ-det (→ᵥₐ-∙ p₁ p₂)         (→ᵥₐ-∙ q₁ q₂) with EvalVec-det p₁ q₁
  ... | refl = →ᵥₐ-det p₂ q₂

  EvalVec-det : ∀ {ds m ts ns₁ ns₂} → EvalVec ds {n = m} ts ns₁ → EvalVec ds ts ns₂ → ns₁ ≡ ns₂
  EvalVec-det eval-[]       eval-[]       = refl
  EvalVec-det (eval-∷ p₁ p₂) (eval-∷ q₁ q₂) = trans (cong _ (→ᵥₐ-det p₁ q₁))
                                                  (cong _ (EvalVec-det p₂ q₂))
