{-# OPTIONS --exact-split #-}

module Propositions where

infixl 5 _↔_
infixl 6 _∨_
infixl 7 _∧_

data ⊥ : Set where

data _∧_ (A B : Set) : Set where
  ∧-intros : A → B → A ∧ B

data _∨_ (A B : Set) : Set where
  ∨-intros₁ : A → A ∨ B
  ∨-intros₂ : B → A ∨ B

data _↔_ (A B : Set) : Set where
  ↔-intros : (A → B) → (B → A) → A ↔ B

¬ : (A : Set) → Set
¬ A = A → ⊥

∧-elim₁ : {A B : Set} → A ∧ B → A
∧-elim₁ (∧-intros a b) = a

∧-elim₂ : {A B : Set} → A ∧ B → B
∧-elim₂ (∧-intros a b) = b

A∧¬A-false : {A : Set} → ¬ (A ∧ ¬ A)
A∧¬A-false (∧-intros a ¬a) = ¬a a

∨-elim : {A B C : Set} → A ∨ B → (A → C) → (B → C) → C
∨-elim (∨-intros₁ a) f g = f a
∨-elim (∨-intros₂ b) f g = g b

↔-elim₁ : {A B : Set} → A ↔ B → A → B
↔-elim₁ (↔-intros f g) = f

↔-elim₂ : {A B : Set} → A ↔ B → B → A
↔-elim₂ (↔-intros f g) = g

-- only this direction is provable apparently
deMorgan : {A B : Set} →  ¬ A ∨ ¬ B → ¬ (A ∧ B)
deMorgan (∨-intros₁ x) (∧-intros x₁ x₂) = x x₁
deMorgan (∨-intros₂ x) (∧-intros x₁ x₂) = x x₂

∧∨distr₁ : {A B C : Set} → (A ∧ B) ∨ C → (A ∨ C) ∧ (B ∨ C)
∧∨distr₁ (∨-intros₁ (∧-intros a b)) = ∧-intros (∨-intros₁ a) (∨-intros₁ b)
∧∨distr₁ (∨-intros₂ c) = ∧-intros (∨-intros₂ c) (∨-intros₂ c)

∧∨distr₂ : {A B C : Set} → (A ∨ C) ∧ (B ∨ C) → (A ∧ B) ∨ C
∧∨distr₂ (∧-intros (∨-intros₁ a) (∨-intros₁ b)) = ∨-intros₁ (∧-intros a b)
∧∨distr₂ (∧-intros (∨-intros₁ a) (∨-intros₂ c)) = ∨-intros₂ c
∧∨distr₂ (∧-intros (∨-intros₂ c) _) = ∨-intros₂ c

∧∨distr : {A B C : Set} → (A ∧ B) ∨ C ↔ (A ∨ C) ∧ (B ∨ C)
∧∨distr = ↔-intros ∧∨distr₁ ∧∨distr₂

∨∧distr₁ : {A B C : Set} → (A ∨ B) ∧ C → (A ∧ C) ∨ (B ∧ C)
∨∧distr₁ (∧-intros (∨-intros₁ a) c) = ∨-intros₁ (∧-intros a c)
∨∧distr₁ (∧-intros (∨-intros₂ b) c) = ∨-intros₂ (∧-intros b c)

∨∧distr₂ : {A B C : Set} → (A ∧ C) ∨ (B ∧ C) → (A ∨ B) ∧ C
∨∧distr₂ (∨-intros₁ (∧-intros a c)) = ∧-intros (∨-intros₁ a) c
∨∧distr₂ (∨-intros₂ (∧-intros b c)) = ∧-intros (∨-intros₂ b) c

∨∧distr : {A B C : Set} → (A ∨ B) ∧ C ↔ (A ∧ C) ∨ (B ∧ C)
∨∧distr = ↔-intros ∨∧distr₁ ∨∧distr₂
