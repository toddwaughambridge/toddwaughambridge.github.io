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
| \:4     = ꞉       \Pi     = Π          |
| \Sigma  = Σ                            |
 ----------------------------------------

This time, we will prove things about dependent types and the identity
type.

\begin{code}

module exercises3 where

open import lecture1 hiding (Type)
open import lecture2 hiding (_×_;×-induction;×-elim;_∘_;¬_)
open import lecture3

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
is-involutive {A} f = {!!}

\end{code}

Exercise 2.
Prove that the Boolean operation `!_` is involutive.

\begin{code}

!-is-involutive : is-involutive !_
!-is-involutive = {!!}

\end{code}

Exercise 3.
The above is not the case in the propositions-as-types logic, because
double-negation elimination does not hold constructively. However,
double negation does.

Prove this statement.

\begin{code}

¬_ : {i : Level} → Type i → Type i
¬ X = X → 𝟘
infix 50 ¬_

¬¬_ : {i : Level} → Type i → Type i
¬¬ X = ¬ (¬ X)

double-negation-introduction : (P : Type) → P → ¬¬ P
double-negation-introduction = {!!}

\end{code}

Exercise 4.
Thorsten asked in the lecture whether it was possible to provide a
type that is undecidable. Prove that it is not (i.e., prove that it
is not the case that the law of excluded middle is false).

\begin{code}

no-undecidable-propositions : (P : Type) → ¬¬ (P + ¬ P)
no-undecidable-propositions = {!!}

\end{code}

Exercise 5.
Prove that the law of excluded middle implies double-negation
elimination.

\begin{code}

LEM-implies-DNE : (Π P ꞉ Type , P + ¬ P) → (Π P ꞉ Type , (¬¬ P → P))
LEM-implies-DNE = {!!}

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
max-split n m = {!!}

\end{code}

Exercise 7.
Prove that the equality type family defined on the natural numbers
(`_≣_`) agrees with the identity type on the natural numbers (`_≡_`).

\begin{code}

_↔_ : Type → Type → Type
A ↔ B = (A → B) × (B → A)

≣-agrees-with-≡ : (n m : ℕ) → (n ≣ m) ↔ (n ≡ m) 
≣-agrees-with-≡ n m = {!!}

\end{code}

** Equality on lists **

Exercise 8.

Define an inductive dependent type `List X` which is either empty or
made up of a head element `x : X` and another list `xs : List X`.

\begin{code}

data List (X : Type) : Type where
 -- Write stuff here

\end{code}

Exercise 9.
Define the function that lifts an element to a singleton list.

\begin{code}

[_] : A → List A
[_] = {!!}

\end{code}

Exercise 10.
Define the append function on lists.

\begin{code}

_++_ : List A → List A → List A
_++_ = {!!}

\end{code}

Exericse 11.
Prove that append has a neutral element.

\begin{code}

++-has-a-left/right-neutral-element
 : Σ e ꞉ List A , ((xs : List A) → (e ++ xs ≡ xs) × (xs ++ e ≡ xs))
++-has-a-left/right-neutral-element
 = {!!}

\end{code}

Exercise 12.
Define the reverse function on lists.

\begin{code}

reverse : List A → List A
reverse = {!!}

\end{code}

Exericse 13. (Hard!)
Prove that `reverse` is involutive.

\begin{code}

reverse-is-involutive : is-involutive (reverse {A})
reverse-is-involutive = {!!}

\end{code}


\end{code}

** Bonus! **

Exercise 14. (Hard!)
Prove that, given any number, there is always a bigger odd number.

\begin{code}

always-a-bigger-odd-number : Π n ꞉ ℕ , Σ (m , _) ꞉ ℕₒ , (n < m)
always-a-bigger-odd-number = {!!}

\end{code}
