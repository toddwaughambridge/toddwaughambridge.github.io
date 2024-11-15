Introduction to Type Theory in Agda
A course given at Midlands Graduate School 2024, Leicester, UK.
Todd Waugh Ambridge, April 2024

Exercise Class 1

** Introduction **

Agda takes some getting used to; it is programming in a very different
way.

The best way to get used to something, is to practice it! Welcome to
the exercise class :-)

 - SHORTCUTS ----------------------------
| C-c C-l         = Load file            |
| C-c C-f         = Next goal            |
| C-c C-c         = Pattern match        |
| C-c C-,         = See context          |
| C-c C-.         = See context and goal |
| C-c C-r         = Refine goal          |
 ----------------------------------------

\begin{code}

module solutions1 where

open import lecture1

{-# BUILTIN NATURAL ℕ #-}

\end{code}

** Defining Basic Functions **

Exercise 1.
Define the identity function.

\begin{code}

id : A → A
id x = x

\end{code}

Exercise 2.
Define the _∘_ operator which composes two functions.

\begin{code}

_∘_ : (g : B → C) (f : A → B) → (A → C)
g ∘ f = λ a → g (f a)

\end{code}

** Defining Functions on Natural Numbers **

Exercise 3.
Define the addition function on natural numbers by using pattern
matching.

\begin{code}

add : ℕ → ℕ → ℕ
add 0        m = m
add (succ n) m = succ (add n m)

\end{code}

Exercise 4.
Define the addition function on natural numbers by using its
elimination principle.

\begin{code}

add' : ℕ → ℕ → ℕ
add' n = ℕ-induction (λ _ → ℕ) n (λ _ r → succ r)

\end{code}

Exercise 5.
Define the multiplication function on natural numbers.

\begin{code}

mul : ℕ → ℕ → ℕ
mul 0 m        = 0
mul (succ n) m = add m (mul n m)

\end{code}

Exercise 6.
Define the maximum function on natural numbers.

\begin{code}

max : ℕ → ℕ → ℕ
max 0 m        = m
max (succ n) 0 = succ n
max (succ n) (succ m) = succ (max n m)

\end{code}

** Defining Inductive Types **

Exercise 7.
Define an inductive type `𝟙` which has one element `⋆ : 𝟙`.

\begin{code}

data 𝟙 : Type where
 ⋆ : 𝟙

\end{code}

Exercise 8.
Define an inductive type `Bool` which has two elements `tt : 𝟚` and
`ff : 𝟚`.

\begin{code}

data Bool : Type where
 tt : Bool
 ff : Bool

\end{code}

Exercise 9.
Define a function that takes a natural number and returns `tt` if it is
an odd number and `ff` otherwise.

\begin{code}

is-odd? : ℕ → Bool
is-odd? 0 = ff
is-odd? 1 = tt
is-odd? (succ (succ n)) = is-odd? n

\end{code}

Exercise 10.
Define an inductive type 𝟘 which has no elements.

\begin{code}

data 𝟘 : Type where

\end{code}
