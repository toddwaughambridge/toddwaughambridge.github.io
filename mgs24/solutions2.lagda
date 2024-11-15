Introduction to Type Theory in Agda
A course given at Midlands Graduate School 2024, Leicester, UK.
Todd Waugh Ambridge, 9 April 2024

Exercise Class 2

** Introduction **

Last time, we picked up a few of Agda's shortcuts and defined a few
functions and types.

 - SHORTCUTS ----------------------------
| C-c C-l         = Load file            |
| C-c C-f         = Next goal            |
| C-c C-c         = Pattern match        |
| C-c C-,         = See context          |
| C-c C-.         = See context and goal |
| C-c C-r         = Refine goal          |
 ----------------------------------------

This time, we will prove some things! Inductive proofs will require
you to get used to `where` clauses to call smaller cases of the same
proof.

As an example, see how we defined `ℕ-induction` in lecture1.

\begin{code}

module solutions2 where

open import lecture1
open import lecture2 hiding (×-induction;×-elim)

\end{code}

** Predicate logic -- Boolean-logic and propositions-as-types **

Exercise 1.
Define the Bool-valued binary function `_xor_` that returns true only
if exactly one of the arguments holds.

\begin{code}

_xor_ : Bool → Bool → Bool
tt xor x = ! x
ff xor x = x

\end{code}

Exercise 2.
Define the function that converts a proposition encoded as a Bool to
one encoded as a type.

\begin{code}

_holds : Bool → Type
tt holds = 𝟙
ff holds = 𝟘
infixl 22 _holds

\end{code}

Exercise 3.
Define logical equivalence in the propositions-as-type logic. Recall
that logical equivalence of `A` and `B` means that `A` and `B` both
imply each other.

\begin{code}

_↔_ : Type → Type → Type
A ↔ B = (A → B) × (B → A)
infix 21 _↔_

\end{code}

Exercise 4.
Prove that your `_xor_` function is correctly related to the `_&&_` and
`_||_` functions.

\begin{code}

xor-is-exclusive-or : (A B : Bool)
                    → ((A || B) holds × ¬ ((A && B) holds))
                    ↔ (A xor B) holds
xor-is-exclusive-or tt tt = (λ (e , f) → f e) , λ ()
xor-is-exclusive-or tt ff = (λ _ → ⋆) , (λ _ → ⋆ , 𝟘-elim)
xor-is-exclusive-or ff tt = (λ _ → ⋆) , (λ _ → ⋆ , 𝟘-elim)
xor-is-exclusive-or ff ff = (λ ()) , (λ ())

\end{code}

Exercise 5.
Define the type family `_⊗_` that can only be constructed if exactly
one of the two argument types is inhabited.

\begin{code}

data _⊗_ (A B : Type) : Type where
 inl : A → ¬ B → A ⊗ B
 inr : B → ¬ A → A ⊗ B
infixl 25 _⊗_

\end{code}

Exercise 6.

Prove that your `_⊗_` type family is correctly related to the `_×_` and
`_+_` type family.

\begin{code}

⊗-is-exclusive-or : ((A + B) × ¬ (A × B)) ↔ A ⊗ B
fst ⊗-is-exclusive-or (inl a , f) = inl a (λ b → f (a , b))
fst ⊗-is-exclusive-or (inr b , f) = inr b (λ a → f (a , b))
snd ⊗-is-exclusive-or (inl a ¬b ) = inl a , λ (_ , b) → ¬b b
snd ⊗-is-exclusive-or (inr b ¬a ) = inr b , λ (a , _) → ¬a a

\end{code}

Exercise 7.

Define and prove  the induction and recursion principles for binary
product types.

\begin{code}

×-induction : (P : A × B → Type)
            → (p : (a : A) (b : B) → P (a , b))
            → (x : A × B) → P x
×-induction P p (a , b) = p a b

×-elim : (A → B → C) → (A × B → C)
×-elim {A} {B} {C} = ×-induction (λ _ → C)

\end{code}

** Logic with natural numbers **

Exercise 8.
Define a type family `_≣_ : ℕ → ℕ → Type` that holds if the two
arguments are equal.

Note: You can define this as a function directly, or inductively using
`data`.

\begin{code}

_≣_ : ℕ → ℕ → Type
0      ≣ 0      = 𝟙
0      ≣ succ m = 𝟘
succ n ≣ 0      = 𝟘
succ n ≣ succ m = n ≣ m

-- data _≣_ : ℕ → ℕ → Type where

\end{code}

Exercise 9.
Prove that your defined type family is indeed an equivalence relation;
i.e., it is reflexive, symmetric and transitive.

\begin{code}

≣-is-reflexive : (n : ℕ) → n ≣ n
≣-is-reflexive zero = ⋆
≣-is-reflexive (succ n)
 = ≣-is-reflexive n

≣-is-symmetric : (n m : ℕ) → n ≣ m → m ≣ n
≣-is-symmetric zero zero p = ⋆
≣-is-symmetric (succ n) (succ m) p
 = ≣-is-symmetric n m p

≣-is-transitive : (n m k : ℕ) → n ≣ m → m ≣ k → n ≣ k
≣-is-transitive zero zero zero p q = ⋆
≣-is-transitive (succ n) (succ m) (succ k) p q
 = ≣-is-transitive n m k p q

\end{code}

Exercise 10.
Prove that the `max` function from the previous exercise sheet is
commutative

\begin{code}

max : ℕ → ℕ → ℕ
max 0        0        = zero
max 0        (succ m) = succ m
max (succ n) 0        = succ n
max (succ n) (succ m) = succ (max m n)

max-is-commutative : (n m : ℕ) → max n m ≣ max m n
max-is-commutative 0        0        = ⋆
max-is-commutative 0        (succ m) = ≣-is-reflexive m
max-is-commutative (succ n) 0        = ≣-is-reflexive n
max-is-commutative (succ n) (succ m) = max-is-commutative m n

\end{code}
