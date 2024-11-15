Introduction to Type Theory in Agda
A course given at Midlands Graduate School 2024, Leicester, UK.
Todd Waugh Ambridge, 8 April 2024

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

 - BACKSLASH CHARACTERS -----------------
| \lambda = λ       \to     = →          |
| \bN     = ℕ       \b0     = 𝟘          |
| \b1     = 𝟙       \st     = ⋆          |
 ----------------------------------------

\begin{code}

module exercises1 where

open import lecture1

\end{code}

** Defining Basic Functions **

Exercise 1.
Define the identity function.

\begin{code}

id : A → A
id = {!!}

\end{code}

Exercise 2.
Define the _∘_ operator which composes two functions.

\begin{code}

_∘_ : (g : B → C) (f : A → B) → (A → C)
_∘_ = {!!}

\end{code}

** Defining Functions on Natural Numbers **

Exercise 3.
Define the addition function on natural numbers by using pattern
matching.

\begin{code}

add : ℕ → ℕ → ℕ
add = {!!}

\end{code}

Exercise 4.
Define the addition function on natural numbers by using its
elimination principle.

\begin{code}

add' : ℕ → ℕ → ℕ
add' n = ℕ-induction {!!} {!!} {!!}

\end{code}

Exercise 5.
Define the multiplication function on natural numbers.

\begin{code}

mul : ℕ → ℕ → ℕ
mul = {!!}

\end{code}

Exercise 6.
Define the maximum function on natural numbers.

\begin{code}

max : ℕ → ℕ → ℕ
max = {!!}

\end{code}

** Defining Inductive Types **

Exercise 7.
Define an inductive type `𝟙` which has one element `⋆ : 𝟙`.

\begin{code}



\end{code}

Exercise 8.
Define an inductive type `Bool` which has two elements `tt : Bool` and
`ff : Bool`.

\begin{code}



\end{code}

Exercise 9.
Define a function that takes a natural number and returns `tt` if it is
an odd number and `ff` otherwise.

\begin{code}

is-odd? : ℕ → {!!}
is-odd? = {!!}

\end{code}

Exercise 10.
Define an inductive type 𝟘 which has no elements.

\begin{code}



\end{code}
