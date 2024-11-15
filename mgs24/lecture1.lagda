Introduction to Type Theory in Agda
A course given at Midlands Graduate School 2024, Leicester, UK.
Todd Waugh Ambridge, April 2024

Lecture 1 -- Introduction

\begin{code}

{-# OPTIONS --without-K --safe #-}
module lecture1 where

\end{code}

** Introduction **

In the final part of this lecture, we will take a look at defining
some basic functions in Agda, and defining the natural numbers.

Agda infamously uses `Set` for the type of types (I believe many of
the implementers now regret this). However, there is a quick fix...

\begin{code}

Type = Set

\end{code}

We add several variables (`A`, `B`, etc.), for types, to our context.

\begin{code}

variable A B C D E : Type

\end{code}

** Defining Basic Functions **

Agda already has built-in support for defining functions.

The syntax of Agda is similar to the syntax of Haskell. For example,
let's define the first projection function that we saw earlier.

\begin{code}

K : A → B → A
K a b = a

\end{code}

The `:` symbol starts the type definition, while the `=` symbol starts
the definition of the term itself.

Defining this function is like adding the following two rules to our
theory:

  A:Type B:Type        A:Type   B:Type
 ---------------    --------------------
    K a b : A          K a b = a : A

We can actually re-define the formation and elimination typing rules
for functions.

\begin{code}

→-Form : (A : Type) (B : Type) → Type
→-Form A B = A → B

→-Elim : (f : A → B) (a : A) → B
→-Elim f a = f (a) -- Also written `f a`

\end{code}

Unfortunately, we cannot define the introduction rule in Agda; it is
instead taken care of directly in Agda's type system.

Note also that the computation rule is derived automatically, as with
the `K` function.

\end{code}

** Natural Numbers **

Agda has built-in support for defining inductive types via the recipe
we discussed earlier, using the keyword `data`.

The formation rule and introduction rules for natural numbers are
given below in a `data` definition.

\begin{code}

data ℕ : Type where -- ℕ-Form
 zero : ℕ           -- ℕ-Intro₀
 succ : ℕ → ℕ       -- ℕ-Introₛ
{-# BUILTIN NATURAL ℕ #-}

\end{code}

Finally, let's formalise the elimination rule of natural numbers.

\begin{code}

-- ℕ-Elim
ℕ-induction : (P : ℕ → Type)
            → (p₀ : P zero) (pₛ : (n : ℕ) → P n → P (succ n))
            → (n : ℕ) → P n

\end{code}

In order to define the elimination rule, we have to give both of its
computation rules. We do this by *pattern matching* on `n : ℕ`.

\begin{code}

ℕ-induction P p₀ pₛ zero     = p₀     -- ℕ-Comp₀
ℕ-induction P p₀ pₛ (succ n) = pₛ n IH  -- ℕ-Compₛ
 where
  IH : P n
  IH = ℕ-induction P p₀ pₛ n 

\end{code}

Agda takes some getting used to; it is programming in a very different
way.

The best way to get used to something, is to practice it! See you in
the exercise class :-)
