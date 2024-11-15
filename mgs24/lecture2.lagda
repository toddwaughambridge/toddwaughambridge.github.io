Introduction to Type Theory in Agda
A course given at Midlands Graduate School 2024, Leicester, UK.
Todd Waugh Ambridge, 9 April 2024

Lecture 2 -- Propositions as types

\begin{code}

{-# OPTIONS --without-K --safe #-}
open import lecture1
module lecture2 where

\end{code}

** Recap **

In the last lecture, we got started with type theory in Agda by
defining the natural numbers as an inductive type.

In the exercise class, we defined some basic functions recursively
by pattern matching...

\begin{code}

add : ℕ → ℕ → ℕ
add zero     m = m
add (succ n) m = succ (add n m)

\end{code}

...and also by using the induction principle, derived from the typing
rules of natural numbers in MLTT.

\begin{code}

add' : ℕ → ℕ → ℕ
add' n = ℕ-induction (λ _ → ℕ) n (λ _ r → succ r)

\end{code}

Note that induction is dependent: it takes a type family `P : ℕ → Type`
and returns a term `n : P n`. But, when `P` is a constant function
(as with `λ _ → ℕ` in the above), we can instead think of this as a
recursion principle.

\begin{code}

ℕ-elim : {X : Type} → X → (ℕ → X → X) → ℕ → X
ℕ-elim {X} = ℕ-induction (λ _ → X)

add'' : ℕ → ℕ → ℕ
add'' n = ℕ-elim n (λ _ → succ)

\end{code}

Defining functions is all well and good, but Agda's true strength comes
from the fact that it is a proof assistant as well as a programming
language.

Recall that, last lecture, we learned that (via the Curry-Howard
correspondence/propositions-as-types interpretation) MLTT corresponds
to constructive predicate logic.

This means that, in our Agda setting, we can directly program proofs
to mathematical statements.

** Boolean Logic **

Before we define a logic based on types, let's look at a logic we
are more familiar with; i.e. logic as defined on the Booleans.

First, let's define a type of Boolean values.

\begin{code}

data Bool : Type where
 tt ff : Bool

\end{code}

We won't worry too much about this type's MLTT typing rules, but its
induction (and, hence, recursion) principle is clear.

\begin{code}

Bool-induction : (P : Bool → Type)
               → (pᵗ : P tt) (pᶠ : P ff) 
               → (x : Bool) → P x 
Bool-induction P pᵗ pᶠ tt = pᵗ
Bool-induction P pᵗ pᶠ ff = pᶠ

Bool-elim : A → A → Bool → A
Bool-elim {A} = Bool-induction (λ _ → A)

\end{code}

Next, let's go as far as interpreting Boolean propositional logic.

In order to interpret propositional logic, we need interpretations of:

 * Truth,

   We have `tt : Bool`.

 * Falsity,

   We have `ff : Bool`.
  
 * Implication,

\begin{code}

_⇒_ : Bool → Bool → Bool
tt ⇒ Q = Q
ff ⇒ Q = tt
-- _⇒_ P = Bool-elim P tt

\end{code}

 * Negation,

\begin{code}

!_ : Bool → Bool
! tt = ff
! ff = tt
infix 50 !_
-- !_ = Bool-elim ff tt 

\end{code}

 * Disjunction.

\begin{code}

_||_ : Bool → Bool → Bool
tt || Q = tt
ff || Q = Q
-- _||_ P = Bool-elim tt P
infixl 4 _||_

\end{code}

 * Conjunction,

\begin{code}

_&&_ : Bool → Bool → Bool
tt && Q = Q
ff && Q = ff
-- _&&_ Q = Bool-elim Q ff
infixl 2 _&&_

\end{code}

Let's see some example computations of logical propositions:

\begin{code}

modus-ponens' : Bool → Bool → Bool
modus-ponens' P Q = ((P ⇒ Q) && P) ⇒ Q

modus-tollendo-ponens' : Bool → Bool → Bool
modus-tollendo-ponens' P Q = ((P || Q) && ! P) ⇒ Q

\end{code}

We can then check whether Agda correctly deduces these statements are true by
computing the answer of their conjunction on all Boolean values.

\begin{code}

run-ex : (Bool → Bool → Bool) → Bool
run-ex ex = ex tt tt
         && ex tt ff
         && ex ff tt
         && ex ff ff

\end{code}

We use (e.g.) `C-c C-n run-ex modus-ponens'` to run the computation.

We can also add numbers to our logic, and define propositions such as
"Is n an odd number?".

\begin{code}

is-odd? : ℕ → Bool
is-odd? 0 = ff
is-odd? 1 = tt
is-odd? (succ (succ n))
 = is-odd? n

is-odd?' : ℕ → Bool
is-odd?' 0 = ff
is-odd?' (succ n) = ! is-odd?' n
-- is-odd?' = ℕ-elim ff (λ _ r → ! r) 

\end{code}

** The Decidability Problem **

So far so good... but the problem with Boolean logic is that it is not very 
expressive. There are many things we would like to reason about that cannot be
captured by a Bool. For example, let's say we want to prove that the
two definitions of `is-odd?` above are equal.

We would first need to define equality on functions (ℕ → Bool). But
how can we do this?

\begin{code}

module Bool-eq where

 _==_ : Bool → Bool → Bool
 tt == Q = Q
 ff == Q = ! Q
 -- _==_ P = Bool-elim P (! P)

 {- _===_ : (ℕ → Bool) → (ℕ → Bool) → Bool

 is-odd-functions-equal : Bool
 is-odd-functions-equal = is-odd? === is-odd?'

 f === g = f 0 == g 0 && ((λ n → f (succ n)) === (λ n → g (succ n))) -}

\end{code}

We need to check whether `f 0 == g 0`, and then `f 1 == g 1`, and then ...
This procedure is clearly never going to terminate if each of these values 
reduces to `tt` -- it will never return an answer. Therefore, we cannot decide 
whether `f === g` should reduce to `tt` or `ff`.

Those propositions `P` that can be reduced to true or false are called
decidable propositions. The law of excluded middle holds for all
decidable propositions:

 P ∨ ¬ P

Of course, if we take `Bool` as our type of propositions, then every 
definable proposition immediately satisfies the law of excluded 
middle by definition of being a Boolean.

\begin{code}

is-decidable' : Bool → Bool
is-decidable' P = P || ! P

lem : Bool
lem = is-decidable' tt && is-decidable' ff

\end{code}

In classical mathematics, every proposition is indeed decidable: the
law of excluded middle holds in general.

But in constructive mathematics, like in programming, if we want to
say that `P` is decidable, we have to actually compute the answer of
whether or not `P` holds. Therefore, the law of excluded middle does
not hold in general, because there are questions that we cannot decide
computationally: for example, the question of whether two programs are
equal, or whether a program halts.

So in constructive type theory, the Booleans will not do as our type of
propositions. We need to use a more general type, that has an
interpretation of truth and falsity, but that we cannot in general
decide whether a given term of that type is true or false.

Using the propositions-as-types interpretation, the type of
propositions is... `Type` itself.

A type can hold (i.e. if we can construct a term of it), it can be
shown to not hold (i.e. if we can prove a term of it cannot be
constructed), but we cannot decide in general whether a term of a given
type can be constructed.

** Propositions as types **

For propositional logic, we need interpretations of:

 * Truth,

   When is a proposition true, constructively? When a proof of the
   proposition can be yielded. If `P` is a type representing a
   proposition, then `p : P` is a proof of that proposition.

   So, if we can exhibit an element of a type, then the proposition
   that type interprets is true.

   But which type should represent base truth itself? Technically, any
   type that we can exhibit a term of can represent truth, but it would
   feel strange to use (for example) `ℕ`.

   This is because there are many elements of `ℕ` and each has a
   different computational meaning. It would be better to choose a type
   that has a single element, so that once we see the element we know
   that this just means "true", with no additional computation content.

   Truth is interpreted by a unit type `𝟙 : Type` -- a type with just
   one element -- which we now define inductively.

\begin{code}

data 𝟙 : Type where
 ⋆ : 𝟙

𝟙-induction : (P : 𝟙 → Type)
            → (p⋆ : P ⋆) 
            → (x : 𝟙) → P x 
𝟙-induction P p⋆ ⋆ = p⋆

𝟙-elim : A → 𝟙 → A
𝟙-elim {A} = 𝟙-induction (λ _ → A)

\end{code}

 * Falsity,

   If truth is an inhabited type, then falsity is an uninhabited type.
   Falsity is interpreted by an empty type `𝟘 : Type` -- a type with no
   introduction rules.

\begin{code}

data 𝟘 : Type where

𝟘-induction : (P : 𝟘 → Type)
            → (x : 𝟘) → P x
𝟘-induction P ()

𝟘-elim : 𝟘 → A
𝟘-elim {A} = 𝟘-induction (λ _ → A)

\end{code}

 * Implication,

   Implication introduction says that `P ⇒ Q` when an assumption of
   that `P` is true leads to the truth of `Q`. With our interpretation
   of truth, this means that any term of `P` allows us to construct a
   term of `Q`.

   So to interpret implication, we need a type whose terms are
   procedures that take terms of `P` and construct terms of `Q`.

   This is just the function type (P → Q)!

   Implication is therefore interpreted by function types. The
   principle of modus ponens is just function application.

\begin{code}

modus-ponens : (A → B) → A → B
modus-ponens f a = f a

\end{code}

   Implication should be transitive -- which is the case for function
   application.
   
\begin{code}

→-transitive : (A → B) → (B → C) → (A → C)
→-transitive f g a = g (f a)

\end{code}

   From a programming point of view, this is just the composition of
   two functions.

\begin{code}

_∘_ : (B → C) → (A → B) → (A → C)
g ∘ f = λ a → g (f a)

\end{code}

 * Negation,

   Negation introduction says that a proposition `P` is false `¬ P` if
   it implies a contradiction.

   What type interprets the idea that `P` leads to a contradiction?
   Hint: Have a think about what would constitute a contradiction to
   our theory.

   Constructing a term `x : 𝟘` would be contradictory! That would say
   that we have a way to introduce a term of a type that has no rules
   of introduction.

   Negation `¬ P` is interpreted as "`P` implies `𝟘`". This is a type
   that we do not define inductively -- it arises from types we have
   already built (i.e. function types and the empty type).

\begin{code}

¬_ : Type → Type
¬ X = X → 𝟘
infix 50 ¬_

modus-tollens : (A → B) → ¬ B → ¬ A
modus-tollens f ¬b = ¬b ∘ f

\end{code}

 * Disjunction,

   Disjunction introduction says that if we have `P` we have `P ∨ Q`,
   and also if we have `Q` we have `P ∨ Q`.

   In imperative programming, this is like a `Union` class. There are
   two constructors: either by constructing an element of `P` or by
   constructing an element of `Q`.

   In MLTT, these are called binary sum types, or tagged unions.

\begin{code}

data _+_ (A B : Type) : Type where
 inl : A → A + B
 inr : B → A + B
infixl 4 _+_

+-induction : (P : A + B → Type)
            → (pa : (a : A) → P (inl a))
            → (pb : (b : B) → P (inr b))
            → (x : A + B) → P x
+-induction P pa pb (inl a) = pa a
+-induction P pa pb (inr b) = pb b

+-elim : {A B X : Type} → ((a : A) → X) → ((b : B) → X) → A + B → X
+-elim {A} {B} {X} = +-induction {A} {B} (λ _ → X)

\end{code}

   Note that the `induction` and `elim` functions for `_+_`-types are
   similar to those for Bool, which makes sense given that both have
   two explicit 'options'. In fact, we can write the `if_then_else_`
   function using `_+_`-types.

\begin{code}

if_then_else_ : A + B → C → C → C
if x then y else z = +-elim (λ _ → y) (λ _ → z) x

\end{code}

   The interpretation of disjunction is the first key difference between 
   classical and constructive logic. 
   
   In classical logic, knowing that `P ∨ Q` holds does not tell you which of 
   the two cases holds.

   In order to decide a disjunction classically, you have to know that
   one of the two sides cannot hold.

\begin{code}

modus-tollendo-ponens : A + B → ¬ A → B
modus-tollendo-ponens (inl a) ¬a = 𝟘-elim (¬a a)
modus-tollendo-ponens (inr b) ¬a = b

\end{code}

   But, in constructive type theory, the 'tag' of the term (i.e. `inl`
   or `inr`) specifies explicitly whether the proof is "in the left" or
   "in the right" side of the disjunction.

 * Conjunction,

   Finally, conjunction introduction says that if we have `P` and `Q`
   then we have `P ∧ Q`.

   In imperative programming, this is like a `Pair` class:

     public class Pair<K,V> {
        private K fst;
        private V snd;

        public K getFst() { return fst; }
        public V getSnd() { return snd; }
     }

   Conjunction is interpreted by these pair types; in MLTT, they are
   called binary product types.

\begin{code}

module ×-data where

 data _×_ (A B : Type) : Type where
  _,_ : A → B → A × B

 ×-induction : {A B : Type}
             → (P : A × B → Type)
             → (p : (a : A) (b : B) → P (a , b))
             → (x : A × B) → P x
 ×-induction P p (x , y) = p x y

\end{code}

   Although the introduction rule for binary product types can be
   defined by giving a single constructor (as above, using `data`), we
   can also define it by giving its two destructors (as below, using
   `record`). In this way, `record`s are like classes in other
   programming languages.

   To put this another way, rather than defining our interpretation of
   conjunction by interpreting conjunction introduction

     A, B ⊢ A ∧ B,

   we define it by interpreting conjunction elimination

     A ∧ B ⊢ A,    A ∧ B ⊢ B.

\begin{code}

record _×_ (A B : Type) : Type where
  
 -- This allows us to define syntax sugar for the resulting
 -- constructor
 constructor _,_ 

 -- We then give each destructor as a field 
 field
  fst : A
  snd : B

 -- Optionally, records can contain methods, just like in other
 -- programming languages. The two below are just illustrative, as we
 -- will always prefer to directly use the eliminators
 getFst : A
 getFst = fst

 getSnd : B
 getSnd = snd

 -- As with modules, we open the record so that we can use the fields
 -- and methods without having to write the name of the record each
 -- time
open _×_
infixl 2 _×_
  
×-induction : (P : A × B → Type)
            → (p : (a : A) (b : B) → P (a , b))
            → (x : A × B) → P x
×-induction P p (a , b) = p a b

×-elim : (A → B → C) → (A × B → C)
×-elim {A} {B} {C} = ×-induction (λ _ → C)

\end{code}

The elimination principle for binary products is just the act of
uncurrying the function. We can of course also curry the function.

\begin{code}

uncurry = ×-elim

curry : (A × B → C) → (A → B → C)
curry f a b = f (a , b)

\end{code}

As with our Boolean logic, let's add numbers to our
propositions-as-types interpretation, so that we can reason about them.

\begin{code}

is-odd : ℕ → Type
is-odd 0 = 𝟘
is-odd 1 = 𝟙
is-odd (succ (succ n))
 = is-odd n

\end{code}

For any `n : ℕ`, the term `is-odd n : Type` is a dependent type,
because it depends on the value of `n : ℕ`.

If `n` is indeed odd, then `is-odd n = 𝟙 : Type`,
                 otherwise `is-odd n = 𝟘 : Type`.
Therefore, if `n` is indeed odd, then `is-odd n` is inhabited
                           otherwise, `is-odd n` is empty.

A term `p : is-odd n` is hence a proof that `n` is odd, because if it
were even, it would have been impossible for us to have constructed
such a term `p`.

\begin{code}

5-is-odd : is-odd 5
5-is-odd = ⋆

84-is-not-odd : ¬ (is-odd 84)
84-is-not-odd ()

\end{code}

We call `is-odd` itself a (dependent) type family.

In today's exercise class, we will reason more about natural numbers.
See you there. :-) 
