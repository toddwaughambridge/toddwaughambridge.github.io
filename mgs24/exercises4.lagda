Introduction to Type Theory in Agda
A course given at Midlands Graduate School 2024, Leicester, UK.
Todd Waugh Ambridge, 11 April 2024

Exercise Class 4

** Introduction **

Last time, we proved equalities to do with booleans, natural numbers
and lists.

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
| \Sigma  = Σ       \cong   = ≅          |
| \eta    = η       \Ge     = ε          |
 ----------------------------------------

This time, we will prove some type equivalences.

\begin{code}

module exercises4 where

open import lecture1 hiding (Type)
open import lecture2 hiding (Bool;_×_;×-induction;×-elim;_∘_;¬_;_+_)
open import lecture3 hiding (is-decidable;DecidableType)
open import lecture4 

open import Agda.Primitive renaming (Set to Type)

\end{code}

** Type equivalences **

Exercise 1.
Prove that the function types `A → B → C` and `A × B → C` are
equivalent.

\begin{code}

≅-curry : {i : Level} (A B C : Type i) → (A → B → C) ≅ (A × B → C)
≅-curry A B C = f , (g , (η , ε)) where
 f : (A → B → C) → A × B → C 
 f = {!!}
 g : (A × B → C) → A → B → C
 g = {!!}
 η : (f ∘ g) ∼ id
 η = {!!}
 ε : (g ∘ f) ∼ id
 ε = {!!}

\end{code}

Exercise 2.
Prove the distributivity rule for type equivalences.

\begin{code}

≅-distributivity
 : {i : Level} (A B C : Type i) → (A + B) × C ≅ (A × C) + (B × C)
≅-distributivity A B C = f , (g , (η , ε)) where
 f : (A + B) × C → (A × C) + (B × C)
 f = {!!}
 g : (A × C) + (B × C) → (A + B) × C
 g = {!!}
 η : (f ∘ g) ∼ id
 η = {!!}
 ε : (g ∘ f) ∼ id
 ε = {!!}

\end{code}

Exercise 3.
Prove that `_≅_` is an equivalence relation.

\begin{code}

≅-refl : {i : Level} (A : Type i) → A ≅ A
≅-refl = ?

≅-sym : {i : Level} (A B : Type i) → A ≅ B → B ≅ A
≅-sym = ?

≅-trans : {i : Level} (A B C : Type i) → A ≅ B → B ≅ C → A ≅ C
≅-trans = ?

\end{code}

Exercise 4.
Prove that `ℕ` is countably infinite by showing it is equivalent to
`ℕ + 𝟙`.

\begin{code}

ℕ-countable : ℕ ≅ ℕ + 𝟙
ℕ-countable = ?

\end{code}

Exercise 5. (Hard!)
Prove that `𝟙` is finite by showing it is not equivalent to
`𝟙 + 𝟙`.

Hint: You will need to first prove that `¬ (inl ⋆ ≡ inr ⋆)`.

\begin{code}

inl-is-not-inr : ¬ (_≡_ {_} {𝟙 + 𝟙} (inl ⋆) (inr ⋆))
inl-is-not-inr ()

𝟙-finite : ¬ (𝟙 ≅ 𝟙 + 𝟙)
𝟙-finite = ?

\end{code}
