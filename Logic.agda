{-# OPTIONS --safe --cubical-compatible #-}

module Logic where

data ⊥ {𝑎} : Set 𝑎 where

¬_ : ∀ {𝑝} → Set 𝑝 → Set 𝑝
¬_ {𝑝} P = P → ⊥ {𝑝}

⊥-elim : ∀ {𝑎 𝑝} {A : Set 𝑎} → ⊥ {𝑝} → A
⊥-elim ()
