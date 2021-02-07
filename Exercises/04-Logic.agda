module 04-Logic where

infixl 6 _∨_
infixl 7 _∧_

-- A → (B → A)
modus-ponens : {A B : Set} → (A → B) → A → B
modus-ponens f a = f a

data _∧_ (A B : Set) : Set where
  both : (a : A) → (b : B) → A ∧ B

data _∨_ (A B : Set) : Set where
  first : (a : A) → A ∨ B
  second : (b : B) → A ∨ B

-- A ∧ B → A
proj1 : {A B : Set} → A ∧ B → A
proj1 (both a b) = a

-- A ∧ B → B
proj2 : {A B : Set} → A ∧ B → B
proj2 (both a b) = b

-- A → A ∨ B
inj1 : {A B : Set} → A → A ∨ B
inj1 = first

-- B → A ∨ B
inj2 : {A B : Set} → B → A ∨ B
inj2 = second

∨-over-∧
  : {A B C : Set}
  → (A ∧ B) ∨ C
  → (A ∨ C) ∧ (B ∨ C)
∨-over-∧ (first (both a b)) = both (first a) (first b)
∨-over-∧ (second x) = both (second x) (second x)

∧-over-∨
  : {A B C : Set}
  → (A ∨ B) ∧ C
  → (A ∧ C) ∨ (B ∧ C)
∧-over-∨ (both (first a) c) = first (both a c)
∧-over-∨ (both (second b) c) = second (both b c)

data Empty : Set where

¬ : (A : Set) → Set
¬ A = A → Empty

empty-to-anything : {A : Set} → Empty → A
empty-to-anything ()

-- (A ∧ B) → ¬ (¬ A ∨ ¬ B)
¬-¬-∧ : {A B : Set} → (A ∧ B) → ¬ (¬ A ∨ ¬ B)
¬-¬-∧ (both a b) (first ae) = ae a
¬-¬-∧ (both a b) (second be) = be b

-- (A ∨ B) → ¬ (¬ A ∧ ¬ B)
¬-¬-∨ : {A B : Set} → (A ∨ B) → ¬ (¬ A ∧ ¬ B)
¬-¬-∨ (first a) (both a₁ b) = a₁ a
¬-¬-∨ (second b) (both a b₁) = b₁ b

-- (¬ A ∨ ¬ B) → ¬ (A ∧ B)
¬-from-∨ : {A B : Set} → (¬ A ∨ ¬ B) → ¬ (A ∧ B)
¬-from-∨ (first a) (both a₁ b) = a a₁
¬-from-∨ (second b) (both a b₁) = b b₁

-- (¬ A ∧ ¬ B) → ¬ (A ∨ B)
¬-from-∧ : {A B : Set} → (¬ A ∧ ¬ B) → ¬ (A ∨ B)
¬-from-∧ (both a b) (first a₁) = a a₁
¬-from-∧ (both a b) (second b₁) = b b₁

-- (A ∧ B) → ¬ (A → ¬ B)
∧-¬-arrow : {A B : Set} → (A ∧ B) → ¬ (A → ¬ B)
∧-¬-arrow (both a b) f = f a b

-- (A → B) → ¬ (A ∧ ¬ B)
arrow-¬-∧-¬ : {A B : Set} → (A → B) → ¬ (A ∧ ¬ B)
arrow-¬-∧-¬ f (both a be) = be (f a)

-- (A ∧ ¬ B) → ¬ (A → B)
∧-¬-¬-arrow : {A B : Set} → (A ∧ ¬ B) → ¬ (A → B)
∧-¬-¬-arrow (both a ¬b) f = ¬b (f a)

-- (A → ¬ B) → ¬ (A ∧ B)
arrow-¬-∧ : {A B : Set} → (A → ¬ B) → ¬ (A ∧ B)
arrow-¬-∧ f ¬a∧b = f (proj1 ¬a∧b) (proj2 ¬a∧b)

-- ¬ (A ∧ B) → (A → ¬ B)
¬-∧-arrow-¬ : {A B : Set} → ¬ (A ∧ B) → (A → ¬ B)
¬-∧-arrow-¬ ¬a∧b a ¬b = ¬a∧b (both a ¬b)

-- (A → B) → ((A → (B → C)) → (A → C))
arrow-trans : {A B C : Set} → (A → B) → ((A → (B → C)) → (A → C))
arrow-trans f g a = g a (f a)

-- A → (B → A ∧ B)
arrow-∧ : {A B : Set} → A → (B → A ∧ B)
arrow-∧ a b = both a b

-- (A → C) → ((B → C) → (A ∨ B → C))
arrow-∨ : {A B C : Set} → (A → C) → ((B → C) → (A ∨ B → C))
arrow-∨ f g (first a) = f a
arrow-∨ f g (second b) = g b

-- (A → B) → ((A → ¬ B) → ¬ A)
arrow-¬s : {A B : Set} → (A → B) → ((A → ¬ B) → ¬ A)
arrow-¬s f g a = g a (f a)

-- ¬ A → (A → B)
¬-arrow : {A B : Set} → ¬ A → (A → B)
¬-arrow f a = empty-to-anything (f a)

-- (A ∨ B) → (¬ A → B)
∨-¬-arrow : {A B : Set} → (A ∨ B) → (¬ A → B)
∨-¬-arrow (first a) ae = empty-to-anything (ae a)
∨-¬-arrow (second b) ae = b

-- (¬ A ∨ B) → (A → B)
¬-∨-arrow : {A B : Set} → (¬ A ∨ B) → (A → B)
¬-∨-arrow (first ¬a) a = empty-to-anything (¬a a)
¬-∨-arrow (second b) a = b


module ApplyExample where
  data X : Set where
    -- construct∨s...
  data A : X → Set where -- ¬e that (A : X → Set)
    given : (x : X) → A x

-- ∀xA(x) → A(t)
apply-example : {X : Set} → {A : X → Set} → ((x : X) → A x) → (t : X) → A t
apply-example f t = f t

-- A(t) → ∃xA(x)
data Pair (X : Set) (A : X → Set) : Set where
  pair : (x : X) → (A x) → Pair X A

-- A(t) → ∃xA(x)
pair-example : {X : Set} → {A : X → Set} → (t : X) → (A t) → Pair X A
pair-example t v = pair t v


-- ¬ (A ∨ B) → (¬ A ∧ ¬ B)
¬-over-∨ : {A B : Set} → ¬ (A ∨ B) → (¬ A ∧ ¬ B)
¬-over-∨ {A} {B} f = both ¬A ¬B
  where
  ¬A : A → Empty
  ¬A x = f (first x)

  ¬B : B → Empty
  ¬B x = f (second x)

-- ¬ (¬ (A ∨ ¬ A))
¬-¬-exclusive-middle : {A : Set} → ¬ (¬ (A ∨ ¬ A))
¬-¬-exclusive-middle {A} f = f A-∨-¬-A
  where
-- f  : A ∨ (A → Empty) → Empty
  ¬-A : ¬ A -- A → Empty
  ¬-A x = f (first x)

  A-∨-¬-A : A ∨ ¬ A -- A ∨ (A → Empty)
  A-∨-¬-A = second ¬-A
