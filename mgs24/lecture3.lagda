Introduction to Type Theory in Agda
A course given at Midlands Graduate School 2024, Leicester, UK.
Todd Waugh Ambridge, 10 April 2024

Lecture 3 -- Dependent types and equality

\begin{code}

{-# OPTIONS --without-K --safe #-}
open import lecture1 hiding (Type)
open import lecture2 hiding (_×_;×-induction;×-elim)
module lecture3 where

open import Agda.Primitive renaming (Set to Type)

\end{code}

** Recap **

In the last lecture, we introduced the propositions-as-types
interpretation in Agda by showing that function types interpret
implication, and further defining:
 * `𝟙` for interpreting truth,
 * `𝟘` for interpreting falsity,
 * `¬_`-types for interpreting negation,
 * `_+_`-types for interpreting disjunction,
 * `_×_`-types for interpreting conjunction.

** Predicate Logic via Dependent Types **

To complete our propositions-as-types interpretation of constructive
logic, we need to interpret the two connectives of predicate logic:
 * Universal quantification   (∀ x ꞉ X , P x),
 * Existential quantification (∃ x ꞉ X , P x).

These quantifiers are interpreted by Martin-Lof's dependent types.

 * Π-Types interpret "for all"

   Above we saw our first dependent type family, `is-odd : ℕ → Type`.
   Actually, this is not the first type family we have seen --- `_+_`
   and `_×_` are type families, as are the functions `P : X → Type` in
   each of the induction principles introduced previously.

   These induction principles also featured dependent functions, i.e.
   `p : (x : X) → P x`. A dependent function is therefore a function
   whose domain type `P x` depends on the value of the given argument.

   Clearly, as we have already seen a fair few dependent functions,
   they are built-in to Agda, just like non-dependent functions.

   Non-dependent functions `f : A → B` are terms of function types.
   Meanwhile, dependent functions `f : (x : X) → Y x` are terms of
   "Π-Types".

   We can align Agda's syntax for Π-Types and MLTT's as follows:

\begin{code}

module pi where

 Π : {X : Type} (Y : X → Type) → Type
 Π {X} Y = (x : X) → Y x

 syntax Π {X} (λ x → y) = Π x ꞉ X , y
 infixr -1 Π

\end{code}

   Note that non-dependent functions are just special cases of
   dependent functions, where the type family `P : X → Type` is
   constant.

      (X → Y) = Π x ꞉ X , Y

   While non-dependent functions interpret implication, dependent
   functions interpret universal quantification. That is, to prove
   That is, to prove `∀ x : X , P x` holds, we need to define a
   dependent function `f : Π x ꞉ X , P x`.

   As an example, let's prove that we can decide whether `is-odd n`
   holds for every `n : ℕ`.

\begin{code}

 is-decidable : Type → Type
 is-decidable X = X + ¬ X

 odd-or-even : Π n ꞉ ℕ , is-decidable (is-odd n)
 odd-or-even 0 = inr 𝟘-elim
 odd-or-even 1 = inl ⋆
 odd-or-even (succ (succ n)) = odd-or-even n

\end{code}

   The above proof is inductive, following the definition of `is-odd`
   itself.

   Let's see another example: first we define the type family `_<_`
   that corresponds to the order on natural numbers. Then, we prove
   that, for every `n : ℕ`, `n < succ n`.

\begin{code}

 _<_ : ℕ → ℕ → Type
 zero   < zero   = 𝟘
 zero   < succ _ = 𝟙
 succ _ < zero   = 𝟘
 succ n < succ m = n < m

 succ-is-bigger : Π n ꞉ ℕ , (n < succ n)
 succ-is-bigger zero = ⋆
 succ-is-bigger (succ n) = succ-is-bigger n

\end{code}

 * Σ-Types interpret "there exists"

   Given a type family `Y : X → Type`, how do we interpret the concept
   that there exists a term `x : X` such that `Y(x) : Type` is true?

   The way existential quantification works is the second key
   difference between constructive and classical logic. Classically,
   we can show that there exists an `x : X` that satisfies `Y(x)` by
   showing that the lack of such an `x : X` leads to a contradiction.

   But this argument doesn't hold in constructive maths:
   constructively, to show that `Y(x)` holds, we have to actually
   specify which `x : X` is satisfactory.

   So, to show that `∃ x : X , Y x`, we need to provide a pair of terms:
     * A term `x : X`, called the 'witness' of `Y`,
     * A proof term `Y x : Type`, which depends on the witness.

   In MLTT, these dependent pairs are called "Σ-Types". As with
   non-dependent pairs `_×_`, we define them using `record`.

\begin{code}

module sigma where

 record Σ {X : Type} (Y : X → Type) : Type where
   constructor _,_
   field
    fst : X
    snd : Y fst

 open Σ

 syntax Σ {X} (λ x → y) = Σ x ꞉ X , y
 infixr -1 Σ
 infixr 4 _,_

 Σ-induction : {X : Type} {Y : X → Type}
             → (P : Σ Y → Type)
             → (p : (w : X) (y : Y w) → P (w , y))
             → (z : Σ Y) → P z
 Σ-induction P p (x , y) = p x y

\end{code}

   We can then define `_×_`-types as the non-dependent case of
   `Σ`-types (as with non-dependent functions and Π-types).

\begin{code}

 _×_ : Type → Type → Type
 A × B = Σ a ꞉ A , B

 ×-induction = Σ-induction

\end{code}

   As an example, let's prove that, for every `n : ℕ`, there exists an
   `m : ℕ` larger than it.

\begin{code}

 open pi

 always-a-bigger-number : Π n ꞉ ℕ , Σ m ꞉ ℕ , n < m
 always-a-bigger-number n = succ n , succ-is-bigger n

\end{code}

   In the above, we chose to specify `succ n` as the witness that there
   is a number bigger than `n`. But we could have chose `succ (succ n)`
   or `add 10000 n`...

   The term that we choose as a witness changes the computational
   content of the resulting proof. Therefore, in constructive
   type theory, the method of proving something is relevant --- not
   just the fact that we have proved it.

   This is called proof relevance.

   Another important point about Σ-types is that they form collections
   in our type theory.

   For example, the type `Σ n ꞉ ℕ , is-odd n` collects every possible
   pair of a number with a proof of its oddness.   

\begin{code}

 ℕₒ : Type
 ℕₒ = Σ is-odd

\end{code}

  Therefore, this type is the type of odd numbers itself.

  But what if we want to collect types themselves? For example, we
  could carve out a subset of our logic that relates to the
  Boolean-logic; i.e., we could define a Σ-type that collects all
  decidable types together.

\begin{code}

-- DecidableType : {!!}
-- DecidableType = Σ X ꞉ Type , is-decidable X

\end{code}

  Well, we could, if not for that we get a type error! What is going on
  here? And how do we fix it? What does `Set₁ != Set` mean???

** Type universes **

I've been deliberately vague about what `Type` itself is. In
Martin-Lof's first type theory (which appeared in a 1971 preprint),
there were terms and there were types -- terms had types, but types
were just types.

This raises the interesting question: what is the type of `Type`?
The 1971 theory had an axiom stating

  Type : Type.

But, similarly to Russell with set theory, Girard showed that this
axiom made the system inconsistent.

So Martin-Lof went back to the drawing board, and built his next type
theory (1972's MLTT) around the idea of countably-many type universes.

  Type : Type₁ : Type₂ : ... .

A type universe is a type whose terms are also types.

Agda also has type universes (but with the annoying name Set).

  Set  : Set₁  : Set₂  : ... .

\begin{code}

-- Type₁ = Set₁

term-of-type-Type₁ : Type₁
term-of-type-Type₁ = Type

\end{code}

So that we don't have to rename a countably infinite number of terms,
let's properly rename `Set` to `Type` using Agda's builtin file for
type universes.

\begin{code}

open import Agda.Primitive renaming (Set to Type)

term-of-type-Type₂ : Type₂
term-of-type-Type₂ = Type₁

\end{code}

In that file, we can see a glimpse of how type universes are
implemented in Agda. The idea is that `Type`, `Type₁`, `Type₂`, etc.
are actually syntax sugars for `Type lzero`, `Type (lsuc lzero)`,
`Type (lsuc (lsuc lzero))`. These objects beginning with `l` are called
universe levels in Agda, whereas `Type lzero` (etc.) are called type
universes.

Now, let's redefine `Π` and `Σ` to correctly use type universes.

\begin{code}

Π : {i j : Level} {X : Type i} (Y : X → Type j) → Type (i ⊔ j)
Π {i} {j} {X} Y = (x : X) → Y x

Pi : {i j : Level} (X : Type i) (Y : X → Type j) → Type (i ⊔ j)
Pi _ Y = Π Y 

syntax Pi X (λ x → y) = Π x ꞉ X , y
infixr -1 Pi

record Σ {i j : Level} {X : Type i} (Y : X → Type j) : Type (i ⊔ j)
 where
  constructor _,_
  field
   fst : X
   snd : Y fst

open Σ public

Sigma : {i j : Level} (X : Type i) (Y : X → Type j) → Type (i ⊔ j)
Sigma _ Y = Σ Y 

syntax Sigma X (λ x → y) = Σ x ꞉ X , y
infixr -1 Sigma

\end{code}

Now let's redefine everything we defined with the old `Π` and `Σ`:

\begin{code}

is-decidable : Type → Type
is-decidable X = X + ¬ X

odd-or-even : Π n ꞉ ℕ , is-decidable (is-odd n)
odd-or-even 0 = inr 𝟘-elim
odd-or-even 1 = inl ⋆
odd-or-even (succ (succ n)) = odd-or-even n

_<_ : ℕ → ℕ → Type
zero   < zero   = 𝟘
zero   < succ _ = 𝟙
succ _ < zero   = 𝟘
succ n < succ m = n < m

succ-is-bigger : Π n ꞉ ℕ , (n < succ n)
succ-is-bigger zero = ⋆
succ-is-bigger (succ n) = succ-is-bigger n

Σ-induction : {X : Type} {Y : X → Type}
            → (P : Σ Y → Type)
            → (p : (w : X) (y : Y w) → P (w , y))
            → (z : Σ Y) → P z
Σ-induction P p (x , y) = p x y

_×_ : {i j : Level} → Type i → Type j → Type (i ⊔ j)
A × B = Σ a ꞉ A , B

×-induction = Σ-induction

always-a-bigger-number : Π n ꞉ ℕ , Σ m ꞉ ℕ , n < m
always-a-bigger-number n = succ n , succ-is-bigger n

ℕₒ : Type
ℕₒ = Σ is-odd
 
\end{code}

Now that we have universes, we can define the type of decidable types:

\begin{code}

DecidableType : Type₁
DecidableType = Σ X ꞉ Type , is-decidable X

\end{code}

** Decidable equality **

We finally have a full, well defined, Type-valued first-order
(predicate) logic. The final step is to have an interpretation of
equality.

In the second exercise class, we played around with this Type-valued
logic. For example, we defined an equality relation on the Booleans...

\begin{code}

_==_ : Bool → Bool → Type
tt == tt = 𝟙
ff == tt = 𝟘
tt == ff = 𝟘
ff == ff = 𝟙

\end{code}

...and one on the natural numbers.

\begin{code}

_≣_ : ℕ → ℕ → Type
zero   ≣ zero   = 𝟙
zero   ≣ succ m = 𝟘
succ n ≣ zero   = 𝟘
succ n ≣ succ m = n ≣ m

\end{code}

It is important to realise here that, given any two terms `a,b : Bool`
(respectively `n,m : ℕ`), `a == b` (respectively `n ≣ m`) is a type.

\begin{code}

term-of-type-Type : Type
term-of-type-Type = 3 ≣ 8

\end{code}

Recall also that, in the exercise class, we showed the equality
relation on the natural numbers is indeed an equality relation: it is
reflexive, symmetric and transitive.

\begin{code}

≣-is-reflexive : (n : ℕ) → n ≣ n
≣-is-reflexive zero = ⋆
≣-is-reflexive (succ n) = ≣-is-reflexive n

≣-is-symmetric : (n m : ℕ) → n ≣ m → m ≣ n
≣-is-symmetric zero zero p = ⋆
≣-is-symmetric (succ n) (succ m) p = ≣-is-symmetric n m p

≣-is-transitive : (n m k : ℕ) → n ≣ m → m ≣ k → n ≣ k
≣-is-transitive zero zero zero p q = ⋆
≣-is-transitive (succ n) (succ m) (succ k) p q
 = ≣-is-transitive n m k p q

\end{code}

The Booleans and the natural numbers have what we call decidable
equality; i.e., given any two terms `a,b : Bool` (respectively
`n,m : ℕ`), the question of whether `a == b` (respectively `n ≣ m`) is
a decidable proposition.

This is the same as saying they are decidable types.

\begin{code}

==-is-decidable : (a b : Bool) → is-decidable (a == b)

≣-is-decidable  : (n m : ℕ)    → is-decidable (n ≣  m)

\end{code}

The first proof is by the fact that truth and falsity are decidable
propositions; i.e. `𝟙` and `𝟘` are decidable types.

\begin{code}

𝟙-is-decidable : is-decidable 𝟙
𝟙-is-decidable = inl ⋆

𝟘-is-decidable : is-decidable 𝟘
𝟘-is-decidable = inr 𝟘-elim

==-is-decidable tt tt = 𝟙-is-decidable
==-is-decidable tt ff = 𝟘-is-decidable
==-is-decidable ff tt = 𝟘-is-decidable
==-is-decidable ff ff = 𝟙-is-decidable

\end{code}

The second proof is also by these facts, and induction.

\begin{code}

≣-is-decidable zero     zero     = 𝟙-is-decidable
≣-is-decidable zero     (succ m) = 𝟘-is-decidable
≣-is-decidable (succ n) zero     = 𝟘-is-decidable
≣-is-decidable (succ n) (succ m) = ≣-is-decidable n m

\end{code}

But, as we discussed last lecture, the law of excluded middle does not
hold constructively -- it is not the case that every proposition is
decidable.

  (This is something that we cannot prove nor disprove in our type
  theory; we could, if we wanted to (which we don't), add it as an
  axiom and our theory would remain consistent.)

It is also not the case that every type has decidable equality;
consider the example of functions from last lecture. We cannot decide
whether or not two functions `f,g : ℕ → Bool` are equal, because any
procedure that could do this cannot be guaranteed to halt.

So, have I lied to you? Because last lecture I entirely motivated the
Type-valued logic by saying we could it to define equality on
functions; i.e., I said we could define a type family

      (ℕ → Bool) → (ℕ → Bool) → Type

But how do we actually go about defining this?

** Propositional equality **

We need to think about equality much more generally. In a first-order
logic with equality, equality is itself considered to be a proposition.
This suggests that, as with the other connectives of predicate logic,
it must be interpreted as a type.

Thus far we have interpreted propositional equality differently for
each type, but this is not necessary. Rather than thinking about
equality as type families

      Bool → Bool → Type,

      ℕ → ℕ → Type,

  or (ℕ → Bool) → (ℕ → Bool) → Type,

let's just think about it as a single type family. This type family
would have to depend on both the type and the two elements of that type
that we are trying to show are equal.

\begin{code}

data _≡_ {i : Level} {X : Type i} : X → X → Type i

\end{code}

But how would we introduce elements of these types? When can we
genuinely decide that two elements `x,y : X` of any type `X : Type`
are equal?

Well... only when they are literally the same thing.

\begin{code}

data _≡_ {_} {X} where
 refl : (x : X) → x ≡ x
infix 0 _≡_

\end{code}

By the above, for any two elements `x,y : X` of the same type
`X : Type` there is a type `x ≡ y : Type` whose terms are
identifications of `x` and `y`.

These types have one single constructor, which states the reflexivity
law of equality: every element `x : X` is equal to itself.
     
Therefore, for now, the only way of introducing a term of these types
is by writing `refl x : x ≡ x`; but we cannot *prove* that this is the
*only* way of identifying two things. This is called Axiom K; it is by
default on in Agda, but I have swithced it off at the top of this file
because it is not provable or disprovable in MLTT.

All we can say for now is that the type `x ≡ y : Type` is definitely
inhabited if `x` and `y` are genuinely (judgementally) equal.

\begin{code}

five-equals-five : 5 ≡ 5
five-equals-five = refl 5

adding-1-≡-succ : (n : ℕ) → add 1 n ≡ succ n
adding-1-≡-succ n = refl (succ n)

\end{code}

In tomorrow's first exercise class, we will reason more about
`Π`-types, `Σ`-types and `_≡_`-types. See you there. :-)
