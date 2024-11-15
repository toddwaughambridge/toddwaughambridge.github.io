Introduction to Type Theory in Agda
A course given at Midlands Graduate School 2024, Leicester, UK.
Todd Waugh Ambridge, 11 April 2024

Exercise Class 3

** Introduction **

Last time, we proved some things inductively -- including some proofs
of equality (but not using the identity type itself).

 - SHORTCUTS ----------------------------
| C-c C-l         = Load file            |
| C-c C-f         = Next goal            |
| C-c C-c         = Pattern match        |
| C-c C-,         = See context          |
| C-c C-.         = See context and goal |
| C-c C-r         = Refine goal          |
 ----------------------------------------

 - BACKSLASH CHARACTERS -----------------
| \lambda = λ       \to     = →          |
| \bN     = ℕ       \b0     = 𝟘          |
| \b1     = 𝟙       \st     = ⋆          |
| \leftrightarrow = ↔                    |
| \neg    = ¬       \otimes = ⊗          |
| \x      = ×       \===    = ≣          |
 ----------------------------------------

This time, we will prove things about dependent types and the identity
type.

\begin{code}

module solutions3 where

open import lecture1 hiding (Type)
open import lecture2 hiding (_×_;×-induction;×-elim;_∘_;¬_)
open import lecture3
module lecture4 where

open import Agda.Primitive renaming (Set to Type)

_∘_ : {i j k : Level} {A : Type i} {B : Type j} {C : Type k}
    → (B → C) → (A → B) → (A → C)
g ∘ f = λ a → g (f a)

\end{code}

** Equality on the booleans **

Exercise 1.
For a given function `f : A → A`, define the notion that this function
is involutive (as a `Π`-type); i.e. for every `x : A`, it is the case
that `f (f x)` equals `x`.

\begin{code}

is-involutive : (f : A → A) → Type
is-involutive {A} f = Π x ꞉ A , (f (f x) ≡ x)

\end{code}

Exercise 2.
Prove that the Boolean operation `!_` is involutive.

\begin{code}

!-is-involutive : is-involutive !_
!-is-involutive tt = refl tt
!-is-involutive ff = refl ff

\end{code}

Exercise 3.
The above is not the case in the propositions-as-types logic, because
double-negation elimination does not hold constructively. However,
double negation does.

Prove this statement.

\begin{code}

¬_ : {i : Level} → Type i → Type i
¬ X = X → 𝟘

¬¬_ : {i : Level} → Type i → Type i
¬¬ X = ¬ (¬ X)

double-negation-introduction : (P : Type) → P → ¬¬ P
double-negation-introduction P p ¬p = ¬p p

\end{code}

Exercise 4.
Thorsten asked in the lecture whether it was possible to provide a
type that is undecidable. Prove that it is not (i.e., prove that it
is not the case that the law of excluded middle is false).

\begin{code}

no-undecidable-propositions : (P : Type) → ¬¬ (P + ¬ P)
no-undecidable-propositions P f = f (inr (λ x → f (inl x)))

\end{code}

Exercise 5.
Prove that the law of excluded middle implies double-negation
elimination.

\begin{code}

LEM-implies-DNE : (Π P ꞉ Type , P + ¬ P) → (Π P ꞉ Type , (¬¬ P → P))
LEM-implies-DNE f P ¬¬p
 = +-elim (λ x → x) (λ ¬p → 𝟘-elim (¬¬p ¬p)) (f P)

\end{code}

** Equality on natural numbers **

Exercise 6.
Recall `max` from the first two exerise sheets, and the `ap-succ` proof
from the third lecture.

\begin{code}

max : ℕ → ℕ → ℕ
max 0        0        = zero
max 0        (succ m) = succ m
max (succ n) 0        = succ n
max (succ n) (succ m) = succ (max n m)

ap-succ : {n m : ℕ} → n ≡ m → succ n ≡ succ m
ap-succ {n} {.n} (refl .n) = refl (succ n)

\end{code}

Now prove that `max n m` is always either `n` or `m`.
Hint: At some point, use `+-elim` from Lecture 2.

\begin{code}

max-split : (n m : ℕ) → (max n m ≡ n) + (max n m ≡ m)
max-split zero zero = inl (refl zero)
max-split zero (succ m) = inr (refl (succ m))
max-split (succ n) zero = inl (refl (succ n))
max-split (succ n) (succ m)
 = +-elim (inl ∘ ap-succ) (inr ∘ ap-succ) (max-split n m)

\end{code}

Exercise 7.
Prove that the equality type family defined on the natural numbers
(`_≣_`) agrees with the identity type on the natural numbers (`_≡_`).

\begin{code}

_↔_ : Type → Type → Type
A ↔ B = (A → B) × (B → A)

≣-agrees-with-≡ : (n m : ℕ) → (n ≣ m) ↔ (n ≡ m) 
≣-agrees-with-≡ zero zero = (λ _ → refl zero) , (λ _ → ⋆)
≣-agrees-with-≡ zero (succ m) = (λ ()) , (λ ())
≣-agrees-with-≡ (succ n) zero = (λ ()) , (λ ())
≣-agrees-with-≡ (succ n) (succ m) = left n m , right n m
 where
  left  : (n m : ℕ) → n ≣ m → succ n ≡ succ m
  left n m n≣m = ap-succ (fst (≣-agrees-with-≡ n m) n≣m)
  right : (n m : ℕ) → succ n ≡ succ m → n ≣ m
  right n m (refl _) = ≣-is-reflexive n

\end{code}

** Equality on lists **

Exercise 8.

Define an inductive dependent type `List X` which is either empty or
made up of a head element `x : X` and another list `xs : List X`.

\begin{code}

data List (X : Type) : Type where
 [] : List X
 _::_ : X → List X → List X

\end{code}

Exercise 9.
Define the function that lifts an element to a singleton list.

\begin{code}

[_] : A → List A
[ x ] = x :: []

\end{code}

Exercise 10.
Define the append function on lists.

\begin{code}

_++_ : List A → List A → List A
[]        ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

\end{code}

Exericse 11.
Prove that append has a neutral element.

\begin{code}

ap-cons : (x : A) (xs ys : List A) → xs ≡ ys → (x :: xs) ≡ (x :: ys)
ap-cons x xs ys (refl xs) = refl (x :: xs)

++-has-a-left/right-neutral-element
 : Σ e ꞉ List A , ((xs : List A) → (e ++ xs ≡ xs) × (xs ++ e ≡ xs))
++-has-a-left/right-neutral-element
 = [] , (λ xs → refl xs , γ xs)
 where
  γ : (xs : List A) → xs ++ [] ≡ xs
  γ [] = refl []
  γ (x :: xs) = ap-cons x (xs ++ []) xs (γ xs)

\end{code}

Exercise 12.
Define the reverse function on lists.

\begin{code}

reverse : List A → List A
reverse [] = []
reverse (x :: xs) = reverse xs ++ [ x ]

\end{code}

Exericse 13. (Hard!)
Prove that `reverse` is involutive.

\begin{code}

trans : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans {x} {y} {z} (refl _) (refl _) = refl _

ap : {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
ap f (refl x) = refl (f x)

reverse-++ : (x : A) (xs : List A)
           → reverse (xs ++ [ x ]) ≡ x :: reverse xs
reverse-++ x [] = refl ([ x ])
reverse-++ x (y :: xs) = ap (_++ [ y ]) (reverse-++ x xs)

reverse-is-involutive : is-involutive (reverse {A})
reverse-is-involutive [] = refl []
reverse-is-involutive (x :: xs)
 = trans
     (reverse-++ x (reverse xs))
     (ap-cons x (reverse (reverse xs)) xs (reverse-is-involutive xs))

\end{code}


\end{code}

** Bonus! **

Exercise 14. (Hard!)
Prove that, given any number, there is always a bigger odd number.

\begin{code}

always-a-bigger-odd-number : Π n ꞉ ℕ , Σ (m , _) ꞉ ℕₒ , (n < m)
always-a-bigger-odd-number zero = (1 , ⋆) , ⋆
always-a-bigger-odd-number (succ zero) = (3 , ⋆) , ⋆
always-a-bigger-odd-number (succ (succ n)) = (succ (succ m) , p) , q
 where
  IH : Σ (m , _) ꞉ ℕₒ , n < m
  IH = always-a-bigger-odd-number n
  m : ℕ
  m = fst (fst IH)
  p : is-odd m
  p = snd (fst IH)
  q : succ (succ n) < succ (succ m)
  q = snd IH

\end{code}
