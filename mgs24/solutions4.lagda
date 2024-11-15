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
 f h (a , b) = h a b
 g : (A × B → C) → A → B → C
 g h a b = h (a , b)
 η : (f ∘ g) ∼ id
 η h = refl h
 ε : (g ∘ f) ∼ id
 ε h = refl h

\end{code}

Exercise 2.
Prove the distributivity rule for type equivalences.

\begin{code}

≅-distributivity
 : {i : Level} (A B C : Type i) → (A + B) × C ≅ (A × C) + (B × C)
≅-distributivity A B C = f , (g , (η , ε)) where
 f : (A + B) × C → (A × C) + (B × C)
 f (inl a , c) = inl (a , c)
 f (inr b , c) = inr (b , c)
 g : (A × C) + (B × C) → (A + B) × C
 g (inl (a , c)) = inl a , c
 g (inr (b , c)) = inr b , c
 η : (f ∘ g) ∼ id
 η (inl (a , c)) = refl (inl (a , c))
 η (inr (b , c)) = refl (inr (b , c))
 ε : (g ∘ f) ∼ id
 ε (inl a , c) = refl (inl a , c)
 ε (inr b , c) = refl (inr b , c)

\end{code}

Exercise 3.
Prove that `_≅_` is an equivalence relation.

\begin{code}

≅-refl : {i : Level} (A : Type i) → A ≅ A
≅-refl A = f , (g , (η , ε)) where
 f : A → A
 f = id
 g : A → A
 g = id
 η : (f ∘ g) ∼ id
 η = refl
 ε : (g ∘ f) ∼ id
 ε = refl

≅-sym : {i : Level} (A B : Type i) → A ≅ B → B ≅ A
≅-sym A B (f , (g , (η , ε))) = g , (f , (ε , η))

≅-trans : {i : Level} (A B C : Type i) → A ≅ B → B ≅ C → A ≅ C
≅-trans A B C (f₁ , (g₁ , (η₁ , ε₁))) (f₂ , (g₂ , (η₂ , ε₂)))
 = (f₂ ∘ f₁) , ((g₁ ∘ g₂) , (η , ε))
 where
  η : ((f₂ ∘ f₁) ∘ (g₁ ∘ g₂)) ∼ id
  η x = trans (ap f₂ (η₁ (g₂ x))) (η₂ x)
  ε : ((g₁ ∘ g₂) ∘ (f₂ ∘ f₁)) ∼ id
  ε x = trans (ap g₁ (ε₂ (f₁ x))) (ε₁ x)

\end{code}

Exercise 4.
Prove that `ℕ` is countably infinite by showing it is equivalent to
`ℕ + 𝟙`.

\begin{code}

ℕ-countable : ℕ ≅ ℕ + 𝟙
ℕ-countable = f , (g , (η , ε)) where
 f : ℕ → ℕ + 𝟙
 f zero     = inr ⋆
 f (succ n) = inl n
 g : ℕ + 𝟙 → ℕ
 g (inl n)  = succ n
 g (inr ⋆)  = zero
 η : (f ∘ g) ∼ id
 η (inl n)  = refl (inl n)
 η (inr ⋆)  = refl (inr ⋆)
 ε : (g ∘ f) ∼ id
 ε zero     = refl zero
 ε (succ n) = refl (succ n)

\end{code}

Exercise 5. (Hard!)
Prove that `𝟙` is finite by showing it is not equivalent to
`𝟙 + 𝟙`.

Hint: You will need to first prove that `¬ (inl ⋆ ≡ inr ⋆)`.

\begin{code}

inl-is-not-inr : ¬ (_≡_ {_} {𝟙 + 𝟙} (inl ⋆) (inr ⋆))
inl-is-not-inr ()

all-units-are-stars : (x : 𝟙) → x ≡ ⋆
all-units-are-stars ⋆ = refl ⋆

𝟙-finite : ¬ (𝟙 ≅ 𝟙 + 𝟙)
𝟙-finite (f , (g , (η , ε))) = inl-is-not-inr fact₇ where
  fact₁ : f (g (inl ⋆)) ≡ inl ⋆
  fact₁ = η (inl ⋆)
  fact₂ : f (g (inr ⋆)) ≡ inr ⋆
  fact₂ = η (inr ⋆)
  fact₃ : g (inl ⋆) ≡ ⋆
  fact₃ = all-units-are-stars (g (inl ⋆))
  fact₄ : g (inr ⋆) ≡ ⋆
  fact₄ = all-units-are-stars (g (inr ⋆))
  fact₅ : f ⋆ ≡ inl ⋆
  fact₅ = trans (ap f (sym fact₃)) fact₁
  fact₆ : f ⋆ ≡ inr ⋆
  fact₆ = trans (ap f (sym fact₄)) fact₂
  fact₇ : _≡_ {_} {𝟙 + 𝟙} (inl ⋆) (inr ⋆)
  fact₇ = trans (sym fact₅) fact₆

\end{code}
