# Logic

In the last chapter, we dealt with equations, inequalities,
and basic mathematical statements like
":math:`x` divides :math:`y`."
Complex mathematical statements are built up from
simple ones like these
using logical terms like "and," "or," "not," and
"if ... then," "every," and "some."
In this chapter, we show you how to work with statements
that are built up in this way.

## Implication and the Universal Quantifier

Consider the statement after the `#check`:

```lean
#check ∀ x : ℝ, 0 ≤ x → |x| = x
```

In words, we would say "for every real number `x`, if `0 ≤ x` then
the absolute value of `x` equals `x`".
We can also have more complicated statements like:

```lean
#check ∀ x y ε : ℝ, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε
```

In words, we would say "for every `x`, `y`, and `ε`,
if `0 < ε ≤ 1`, the absolute value of `x` is less than `ε`,
and the absolute value of `y` is less than `ε`,
then the absolute value of `x * y` is less than `ε`."
In Lean, in a sequence of implications there are
implicit parentheses grouped to the right.
So the expression above means
"if `0 < ε` then if `ε ≤ 1` then if `|x| < ε` ..."
As a result, the expression says that all the
assumptions together imply the conclusion.

You have already seen that even though the universal quantifier
in this statement
ranges over objects and the implication arrows introduce hypotheses,
Lean treats the two in very similar ways.
In particular, if you have proved a theorem of that form,
you can apply it to objects and hypotheses in the same way.
We will use as an example the following statement that we will help you to prove a bit later:

```lean
theorem my_lemma : ∀ x y ε : ℝ, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε :=
  sorry

section
variable (a b δ : ℝ)
variable (h₀ : 0 < δ) (h₁ : δ ≤ 1)
variable (ha : |a| < δ) (hb : |b| < δ)

#check my_lemma a b δ
#check my_lemma a b δ h₀ h₁
#check my_lemma a b δ h₀ h₁ ha hb

end
```

You have also already seen that it is common in Lean
to use curly brackets to make quantified variables implicit
when they can be inferred from subsequent hypotheses.
When we do that, we can just apply a lemma to the hypotheses without
mentioning the objects.

```lean
theorem my_lemma2 : ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε :=
  sorry

section
variable (a b δ : ℝ)
variable (h₀ : 0 < δ) (h₁ : δ ≤ 1)
variable (ha : |a| < δ) (hb : |b| < δ)

#check my_lemma2 h₀ h₁ ha hb

end
```

At this stage, you also know that if you use
the `apply` tactic to apply `my_lemma`
to a goal of the form `|a * b| < δ`,
you are left with new goals that require you to prove
each of the hypotheses.

To prove a statement like this, use the `intro` tactic.
Take a look at what it does in this example:

```lean
theorem my_lemma3 :
    ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  intro x y ε epos ele1 xlt ylt
  sorry
```

We can use any names we want for the universally quantified variables;
they do not have to be `x`, `y`, and `ε`.
Notice that we have to introduce the variables
even though they are marked implicit:
making them implicit means that we leave them out when
we write an expression _using_ `my_lemma`,
but they are still an essential part of the statement
that we are proving.
After the `intro` command,
the goal is what it would have been at the start if we
listed all the variables and hypotheses _before_ the colon,
as we did in the last section.
In a moment, we will see why it is sometimes necessary to
introduce variables and hypotheses after the proof begins.

To help you prove the lemma, we will start you off:

```lean
theorem my_lemma4 :
    ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  intro x y ε epos ele1 xlt ylt
  calc
    |x * y| = |x| * |y| := sorry
    _ ≤ |x| * ε := sorry
    _ < 1 * ε := sorry
    _ = ε := sorry

```

Finish the proof using the theorems
`abs_mul`, `mul_le_mul`, `abs_nonneg`,
`mul_lt_mul_right`, and `one_mul`.
Remember that you can find theorems like these using
Ctrl-space completion (or Cmd-space completion on a Mac).
Remember also that you can use `.mp` and `.mpr`
or `.1` and `.2` to extract the two directions
of an if-and-only-if statement.

Universal quantifiers are often hidden in definitions,
and Lean will unfold definitions to expose them when necessary.
For example, let's define two predicates,
`FnUb f a` and `FnLb f a`,
where `f` is a function from the real numbers to the real
numbers and `a` is a real number.
The first says that `a` is an upper bound on the
values of `f`,
and the second says that `a` is a lower bound
on the values of `f`.

```lean
def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x
```

In the next example, `fun x ↦ f x + g x` is the
function that maps `x` to `f x + g x`. Going from the expression `f x + g x`
to this function is called a lambda abstraction in type theory.

```lean
example (hfa : FnUb f a) (hgb : FnUb g b) : FnUb (fun x ↦ f x + g x) (a + b) := by
  intro x
  dsimp
  apply add_le_add
  apply hfa
  apply hgb
```

Applying `intro` to the goal `FnUb (fun x ↦ f x + g x) (a + b)`
forces Lean to unfold the definition of `FnUb`
and introduce `x` for the universal quantifier.
The goal is then `(fun (x : ℝ) ↦ f x + g x) x ≤ a + b`.
But applying `(fun x ↦ f x + g x)` to `x` should result in `f x + g x`,
and the `dsimp` command performs that simplification.
(The "d" stands for "definitional.")
You can delete that command and the proof still works;
Lean would have to perform that contraction anyhow to make
sense of the next `apply`.
The `dsimp` command simply makes the goal more readable
and helps us figure out what to do next.
Another option is to use the `change` tactic
by writing `change f x + g x ≤ a + b`.
This helps make the proof more readable,
and gives you more control over how the goal is transformed.

The rest of the proof is routine.
The last two `apply` commands force Lean to unfold the definitions
of `FnUb` in the hypotheses.
Try carrying out similar proofs of these:

```lean
example (hfa : FnLb f a) (hgb : FnLb g b) : FnLb (fun x ↦ f x + g x) (a + b) :=
  sorry

example (nnf : FnLb f 0) (nng : FnLb g 0) : FnLb (fun x ↦ f x * g x) 0 :=
  sorry

example (hfa : FnUb f a) (hgb : FnUb g b) (nng : FnLb g 0) (nna : 0 ≤ a) :
    FnUb (fun x ↦ f x * g x) (a * b) :=
  sorry
```

Even though we have defined `FnUb` and `FnLb` for functions
from the reals to the reals,
you should recognize that the definitions and proofs are much
more general.
The definitions make sense for functions between any two types
for which there is a notion of order on the codomain.
Checking the type of the theorem `add_le_add` shows that it holds
of any structure that is an "ordered additive commutative monoid";
the details of what that means don't matter now,
but it is worth knowing that the natural numbers, integers, rationals,
and real numbers are all instances.
So if we prove the theorem `fnUb_add` at that level of generality,
it will apply in all these instances.

```lean
variable {α : Type*} {R : Type*} [OrderedCancelAddCommMonoid R]

#check add_le_add

def FnUb' (f : α → R) (a : R) : Prop :=
  ∀ x, f x ≤ a

theorem fnUb_add {f g : α → R} {a b : R} (hfa : FnUb' f a) (hgb : FnUb' g b) :
    FnUb' (fun x ↦ f x + g x) (a + b) := fun x ↦ add_le_add (hfa x) (hgb x)
```

You have already seen square brackets like these in
Section :numref:`proving_identities_in_algebraic_structures`,
though we still haven't explained what they mean.
For concreteness, we will stick to the real numbers
for most of our examples,
but it is worth knowing that Mathlib contains definitions and theorems
that work at a high level of generality.

For another example of a hidden universal quantifier,
Mathlib defines a predicate `Monotone`,
which says that a function is nondecreasing in its arguments:

```lean
example (f : ℝ → ℝ) (h : Monotone f) : ∀ {a b}, a ≤ b → f a ≤ f b :=
  @h
```

The property `Monotone f` is defined to be exactly the expression
after the colon. We need to put the `@` symbol before `h` because
if we don't,
Lean expands the implicit arguments to `h` and inserts placeholders.

Proving statements about monotonicity
involves using `intro` to introduce two variables,
say, `a` and `b`, and the hypothesis `a ≤ b`.
To _use_ a monotonicity hypothesis,
you can apply it to suitable arguments and hypotheses,
and then apply the resulting expression to the goal.
Or you can apply it to the goal and let Lean help you
work backwards by displaying the remaining hypotheses
as new subgoals.

```lean
example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f x + g x := by
  intro a b aleb
  apply add_le_add
  apply mf aleb
  apply mg aleb
```

When a proof is this short, it is often convenient
to give a proof term instead.
To describe a proof that temporarily introduces objects
`a` and `b` and a hypothesis `aleb`,
Lean uses the notation `fun a b aleb ↦ ...`.
This is analogous to the way that an expression
like `fun x ↦ x^2` describes a function
by temporarily naming an object, `x`,
and then using it to describe a value.
So the `intro` command in the previous proof
corresponds to the lambda abstraction in the next proof term.
The `apply` commands then correspond to building
the application of the theorem to its arguments.

```lean
example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f x + g x :=
  fun a b aleb ↦ add_le_add (mf aleb) (mg aleb)
```

Here is a useful trick: if you start writing
the proof term `fun a b aleb ↦ _` using
an underscore where the rest of the
expression should go,
Lean will flag an error,
indicating that it can't guess the value of that expression.
If you check the Lean Goal window in VS Code or
hover over the squiggly error marker,
Lean will show you the goal that the remaining
expression has to solve.

Try proving these, with either tactics or proof terms:

```lean
example {c : ℝ} (mf : Monotone f) (nnc : 0 ≤ c) : Monotone fun x ↦ c * f x :=
  sorry

example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f (g x) :=
  sorry
```

Here are some more examples.
A function :math:`f` from $\mathbb{R}$ to $\mathbb{R}$ is said to be _even_ if
$f(-x) = f(x)$ for every $x$,
and _odd_ if $f(-x) = -f(x)$ for every $x$.
The following example defines these two notions formally
and establishes one fact about them.
You can complete the proofs of the others.

```lean
def FnEven (f : ℝ → ℝ) : Prop :=
  ∀ x, f x = f (-x)

def FnOdd (f : ℝ → ℝ) : Prop :=
  ∀ x, f x = -f (-x)

example (ef : FnEven f) (eg : FnEven g) : FnEven fun x ↦ f x + g x := by
  intro x
  calc
    (fun x ↦ f x + g x) x = f x + g x := rfl
    _ = f (-x) + g (-x) := by rw [ef, eg]


example (of : FnOdd f) (og : FnOdd g) : FnEven fun x ↦ f x * g x := by
  sorry

example (ef : FnEven f) (og : FnOdd g) : FnOdd fun x ↦ f x * g x := by
  sorry

example (ef : FnEven f) (og : FnOdd g) : FnEven fun x ↦ f (g x) := by
  sorry
```

The first proof can be shortened using `dsimp` or `change`
to get rid of the lambda abstraction.
But you can check that the subsequent `rw` won't work
unless we get rid of the lambda abstraction explicitly,
because otherwise it cannot find the patterns `f x` and `g x`
in the expression.
Contrary to some other tactics, `rw` operates on the syntactic level,
it won't unfold definitions or apply reductions for you
(it has a variant called `erw` that tries a little harder in this
direction, but not much harder).

You can find implicit universal quantifiers all over the place,
once you know how to spot them.

Mathlib includes a good library for manipulating sets. Recall that Lean does not
use foundations based on set theory, so here the word set has its mundane meaning
of a collection of mathematical objects of some given type `α`.
If `x` has type `α` and `s` has type `Set α`, then `x ∈ s` is a proposition
that asserts that `x` is an element of `s`. If `y` has some different type `β` then the
expression `y ∈ s` makes no sense. Here "makes no sense" means "has no type hence Lean does not
accept it as a well-formed statement". This contrasts with Zermelo-Fraenkel set theory for instance
where `a ∈ b` is a well-formed statement for every mathematical objects `a` and `b`.
For instance `sin ∈ cos` is a well-formed statement in ZF. This defect of set theoretic
foundations is an important motivation for not using it in a proof assistant which is meant to assist
us by detecting meaningless expressions. In Lean `sin` has type `ℝ → ℝ` and `cos` has type
`ℝ → ℝ` which is not equal to `Set (ℝ → ℝ)`, even after unfolding definitions, so the statement
`sin ∈ cos` makes no sense.
One can also use Lean to work on set theory itself. For instance the independence of the continuum
hypothesis from the axioms of Zermelo-Fraenkel has been formalized in Lean. But such a meta-theory
of set theory is completely beyond the scope of this book.

If `s` and `t` are of type `Set α`,
then the subset relation `s ⊆ t` is defined to mean
`∀ {x : α}, x ∈ s → x ∈ t`.
The variable in the quantifier is marked implicit so that
given `h : s ⊆ t` and `h' : x ∈ s`,
we can write `h h'` as justification for `x ∈ t`.
The following example provides a tactic proof and a proof term
justifying the reflexivity of the subset relation,
and asks you to do the same for transitivity.

```lean
variable {α : Type*} (r s t : Set α)

example : s ⊆ s := by
  intro x xs
  exact xs

theorem Subset.refl : s ⊆ s := fun x xs ↦ xs

theorem Subset.trans : r ⊆ s → s ⊆ t → r ⊆ t := by
  sorry
```

Just as we defined `FnUb` for functions,
we can define `SetUb s a` to mean that `a`
is an upper bound on the set `s`,
assuming `s` is a set of elements of some type that
has an order associated with it.
In the next example, we ask you to prove that
if `a` is a bound on `s` and `a ≤ b`,
then `b` is a bound on `s` as well.

```lean
variable {α : Type*} [PartialOrder α]
variable (s : Set α) (a b : α)

def SetUb (s : Set α) (a : α) :=
  ∀ x, x ∈ s → x ≤ a

example (h : SetUb s a) (h' : a ≤ b) : SetUb s b :=
  sorry
```

We close this section with one last important example.
A function :math:`f` is said to be _injective_ if for
every :math:`x_1` and :math:`x_2`,
if :math:`f(x_1) = f(x_2)` then :math:`x_1 = x_2`.
Mathlib defines `Function.Injective f` with
`x₁` and `x₂` implicit.
The next example shows that, on the real numbers,
any function that adds a constant is injective.
We then ask you to show that multiplication by a nonzero
constant is also injective, using the lemma name in the example as a source
of inspiration. Recall you should use Ctrl-space completion after guessing the beginning of
a lemma name.

```lean
open Function

example (c : ℝ) : Injective fun x ↦ x + c := by
  intro x₁ x₂ h'
  exact (add_left_inj c).mp h'

example {c : ℝ} (h : c ≠ 0) : Injective fun x ↦ c * x := by
  sorry
```

Finally, show that the composition of two injective functions is injective:

```lean
variable {α : Type*} {β : Type*} {γ : Type*}
variable {g : β → γ} {f : α → β}

example (injg : Injective g) (injf : Injective f) : Injective fun x ↦ g (f x) := by
  sorry
```

## The Existential Quantifier

The existential quantifier, which can be entered as `\ex` in VS Code,
is used to represent the phrase "there exists."
The formal expression `∃ x : ℝ, 2 < x ∧ x < 3` in Lean says
that there is a real number between 2 and 3.
(We will discuss the conjunction symbol, `∧`, in :numref:`conjunction_and_biimplication`.)
The canonical way to prove such a statement is to exhibit a real number
and show that it has the stated property.
The number 2.5, which we can enter as `5 / 2`
or `(5 : ℝ) / 2` when Lean cannot infer from context that we have
the real numbers in mind, has the required property,
and the `norm_num` tactic can prove that it meets the description.

There are a few ways we can put the information together.
Given a goal that begins with an existential quantifier,
the `use` tactic is used to provide the object,
leaving the goal of proving the property.

```lean
example : ∃ x : ℝ, 2 < x ∧ x < 3 := by
  use 5 / 2
  norm_num
```

You can give the `use` tactic proofs as well as data:

```lean
example : ∃ x : ℝ, 2 < x ∧ x < 3 := by
  have h1 : 2 < (5 : ℝ) / 2 := by norm_num
  have h2 : (5 : ℝ) / 2 < 3 := by norm_num
  use 5 / 2, h1, h2
```

In fact, the `use` tactic automatically tries to use available assumptions as well.

```lean
example : ∃ x : ℝ, 2 < x ∧ x < 3 := by
  have h : 2 < (5 : ℝ) / 2 ∧ (5 : ℝ) / 2 < 3 := by norm_num
  use 5 / 2
```

Alternatively, we can use Lean's _anonymous constructor_ notation
to construct a proof of an existential quantifier.

```lean
example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
  have h : 2 < (5 : ℝ) / 2 ∧ (5 : ℝ) / 2 < 3 := by norm_num
  ⟨5 / 2, h⟩
```

Notice that there is no `by`; here we are giving an explicit proof term.
The left and right angle brackets,
which can be entered as `\<` and `\>` respectively,
tell Lean to put together the given data using
whatever construction is appropriate
for the current goal.
We can use the notation without going first into tactic mode:

```lean
example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
  ⟨5 / 2, by norm_num⟩
```

So now we know how to _prove_ an exists statement.
But how do we _use_ one?
If we know that there exists an object with a certain property,
we should be able to give a name to an arbitrary one
and reason about it.
For example, remember the predicates `FnUb f a` and `FnLb f a`
from the last section,
which say that `a` is an upper bound or lower bound on `f`,
respectively.
We can use the existential quantifier to say that "`f` is bounded"
without specifying the bound:

```lean
def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

def FnHasUb (f : ℝ → ℝ) :=
  ∃ a, FnUb f a

def FnHasLb (f : ℝ → ℝ) :=
  ∃ a, FnLb f a
```

We can use the theorem `FnUb_add` from the last section
to prove that if `f` and `g` have upper bounds,
then so does `fun x ↦ f x + g x`.

```lean
variable {f g : ℝ → ℝ}

example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
  rcases ubf with ⟨a, ubfa⟩
  rcases ubg with ⟨b, ubgb⟩
  use a + b
  apply fnUb_add ubfa ubgb
```

The `rcases` tactic unpacks the information
in the existential quantifier.
The annotations like `⟨a, ubfa⟩`, written with the
same angle brackets as the anonymous constructors,
are known as _patterns_, and they describe the information
that we expect to find when we unpack the main argument.
Given the hypothesis `ubf` that there is an upper bound
for `f`,
`rcases ubf with ⟨a, ubfa⟩` adds a new variable `a`
for an upper bound to the context,
together with the hypothesis `ubfa` that it has the given property.
The goal is left unchanged;
what _has_ changed is that we can now use
the new object and the new hypothesis
to prove the goal.
This is a common method of reasoning in mathematics:
we unpack objects whose existence is asserted or implied
by some hypothesis, and then use it to establish the existence
of something else.

Try using this method to establish the following.
You might find it useful to turn some of the examples
from the last section into named theorems,
as we did with `fn_ub_add`,
or you can insert the arguments directly
into the proofs.

```lean
example (lbf : FnHasLb f) (lbg : FnHasLb g) : FnHasLb fun x ↦ f x + g x := by
  sorry

example {c : ℝ} (ubf : FnHasUb f) (h : c ≥ 0) : FnHasUb fun x ↦ c * f x := by
  sorry
```

The "r" in `rcases` stands for "recursive," because it allows
us to use arbitrarily complex patterns to unpack nested data.
The `rintro` tactic
is a combination of `intro` and `rcases`:

```lean
example : FnHasUb f → FnHasUb g → FnHasUb fun x ↦ f x + g x := by
  rintro ⟨a, ubfa⟩ ⟨b, ubgb⟩
  exact ⟨a + b, fnUb_add ubfa ubgb⟩
```

In fact, Lean also supports a pattern-matching fun
in expressions and proof terms:

```lean
example : FnHasUb f → FnHasUb g → FnHasUb fun x ↦ f x + g x :=
  fun ⟨a, ubfa⟩ ⟨b, ubgb⟩ ↦ ⟨a + b, fnUb_add ubfa ubgb⟩
```

The task of unpacking information in a hypothesis is
so important that Lean and Mathlib provide a number of
ways to do it. For example, the `obtain` tactic provides suggestive syntax:

```lean
example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
  obtain ⟨a, ubfa⟩ := ubf
  obtain ⟨b, ubgb⟩ := ubg
  exact ⟨a + b, fnUb_add ubfa ubgb⟩
```

Think of the first `obtain` instruction as matching the "contents" of `ubf`
with the given pattern and assigning the components to the named variables.
`rcases` and `obtain` are said to `destruct` their arguments, though
there is a small difference in that `rcases` clears `ubf` from the context
when it is done, whereas it is still present after `obtain`.

Lean also supports syntax that is similar to that used in other functional programming
languages:

```lean
example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
  cases ubf
  case intro a ubfa =>
    cases ubg
    case intro b ubgb =>
      exact ⟨a + b, fnUb_add ubfa ubgb⟩

example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
  cases ubf
  next a ubfa =>
    cases ubg
    next b ubgb =>
      exact ⟨a + b, fnUb_add ubfa ubgb⟩

example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
  match ubf, ubg with
    | ⟨a, ubfa⟩, ⟨b, ubgb⟩ =>
      exact ⟨a + b, fnUb_add ubfa ubgb⟩

example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x :=
  match ubf, ubg with
    | ⟨a, ubfa⟩, ⟨b, ubgb⟩ =>
      ⟨a + b, fnUb_add ubfa ubgb⟩
```

In the first example, if you put your cursor after `cases ubf`,
you will see that the tactic produces a single goal, which Lean has tagged
`intro`. (The particular name chosen comes from the internal name for
the axiomatic primitive that builds a proof of an existential statement.)
The `case` tactic then names the components. The second example is similar,
except using `next` instead of `case` means that you can avoid mentioning
`intro`. The word `match` in the last two examples highlights that
what we are doing here is what computer scientists call "pattern matching."
Notice that the third proof begins by `by`, after which the tactic version
of `match` expects a tactic proof on the right side of the arrow.
The last example is a proof term: there are no tactics in sight.

For the rest of this book, we will stick to `rcases`, `rintro`, and `obtain`,
as the preferred ways of using an existential quantifier.
But it can't hurt to see the alternative syntax, especially if there is
a chance you will find yourself in the company of computer scientists.

To illustrate one way that `rcases` can be used,
we prove an old mathematical chestnut:
if two integers `x` and `y` can each be written as
a sum of two squares,
then so can their product, `x * y`.
In fact, the statement is true for any commutative
ring, not just the integers.
In the next example, `rcases` unpacks two existential
quantifiers at once.
We then provide the magic values needed to express `x * y`
as a sum of squares as a list to the `use` statement,
and we use `ring` to verify that they work.

```lean
variable {α : Type*} [CommRing α]

def SumOfSquares (x : α) :=
  ∃ a b, x = a ^ 2 + b ^ 2

theorem sumOfSquares_mul {x y : α} (sosx : SumOfSquares x) (sosy : SumOfSquares y) :
    SumOfSquares (x * y) := by
  rcases sosx with ⟨a, b, xeq⟩
  rcases sosy with ⟨c, d, yeq⟩
  rw [xeq, yeq]
  use a * c - b * d, a * d + b * c
  ring
```

This proof doesn't provide much insight,
but here is one way to motivate it.
A _Gaussian integer_ is a number of the form $a + bi$
where $a$ and $b$ are integers and $i = \sqrt{-1}$.
The _norm_ of the Gaussian integer $a + bi$ is, by definition,
$a^2 + b^2$.
So the norm of a Gaussian integer is a sum of squares,
and any sum of squares can be expressed in this way.
The theorem above reflects the fact that norm of a product of
Gaussian integers is the product of their norms:
if $x$ is the norm of $a + bi$ and
$y$ in the norm of $c + di$,
then $xy$ is the norm of $(a + bi) (c + di)$.
Our cryptic proof illustrates the fact that
the proof that is easiest to formalize isn't always
the most perspicuous one.
In :numref:`section_building_the_gaussian_integers`,
we will provide you with the means to define the Gaussian
integers and use them to provide an alternative proof.

The pattern of unpacking an equation inside an existential quantifier
and then using it to rewrite an expression in the goal
comes up often,
so much so that the `rcases` tactic provides
an abbreviation:
if you use the keyword `rfl` in place of a new identifier,
`rcases` does the rewriting automatically (this trick doesn't work
with pattern-matching lambdas).

```lean
theorem sumOfSquares_mul' {x y : α} (sosx : SumOfSquares x) (sosy : SumOfSquares y) :
    SumOfSquares (x * y) := by
  rcases sosx with ⟨a, b, rfl⟩
  rcases sosy with ⟨c, d, rfl⟩
  use a * c - b * d, a * d + b * c
  ring
```

As with the universal quantifier,
you can find existential quantifiers hidden all over
if you know how to spot them.
For example, divisibility is implicitly an "exists" statement.

```lean
example (divab : a ∣ b) (divbc : b ∣ c) : a ∣ c := by
  rcases divab with ⟨d, beq⟩
  rcases divbc with ⟨e, ceq⟩
  rw [ceq, beq]
  use d * e; ring
```

And once again, this provides a nice setting for using
`rcases` with `rfl`.
Try it out in the proof above.
It feels pretty good!

Then try proving the following:

```lean
example (divab : a ∣ b) (divac : a ∣ c) : a ∣ b + c := by
  sorry
```

For another important example, a function $f : \alpha \to \beta$
is said to be _surjective_ if for every $y$ in the
codomain, $\beta$,
there is an $x$ in the domain, $\alpha$,
such that $f(x) = $`.
Notice that this statement includes both a universal
and an existential quantifier, which explains
why the next example makes use of both `intro`and`use`.

```lean
example {c : ℝ} : Surjective fun x ↦ x + c := by
  intro x
  use x - c
  dsimp; ring
```

Try this example yourself using the theorem `mul_div_cancel₀`.:

```lean
example {c : ℝ} (h : c ≠ 0) : Surjective fun x ↦ c * x := by
  sorry
```

At this point, it is worth mentioning that there is a tactic, `field_simp`,
that will often clear denominators in a useful way.
It can be used in conjunction with the `ring` tactic.

```lean
example (x y : ℝ) (h : x - y ≠ 0) : (x ^ 2 - y ^ 2) / (x - y) = x + y := by
  field_simp [h]
  ring
```

The next example uses a surjectivity hypothesis
by applying it to a suitable value.
Note that you can use `rcases` with any expression,
not just a hypothesis.

```lean
example {f : ℝ → ℝ} (h : Surjective f) : ∃ x, f x ^ 2 = 4 := by
  rcases h 2 with ⟨x, hx⟩
  use x
  rw [hx]
  norm_num
```

See if you can use these methods to show that
the composition of surjective functions is surjective.

```lean
variable {α : Type*} {β : Type*} {γ : Type*}
variable {g : β → γ} {f : α → β}

example (surjg : Surjective g) (surjf : Surjective f) : Surjective fun x ↦ g (f x) := by
  sorry
```

## Negation

The symbol `¬` is meant to express negation,
so `¬ x < y` says that `x` is not less than `y`,
`¬ x = y` (or, equivalently, `x ≠ y`) says that
`x` is not equal to `y`,
and `¬ ∃ z, x < z ∧ z < y` says that there does not exist a `z`
strictly between `x` and `y`.
In Lean, the notation `¬ A` abbreviates `A → False`,
which you can think of as saying that `A` implies a contradiction.
Practically speaking, this means that you already know something
about how to work with negations:
you can prove `¬ A` by introducing a hypothesis `h : A`
and proving `False`,
and if you have `h : ¬ A` and `h' : A`,
then applying `h` to `h'` yields `False`.

To illustrate, consider the irreflexivity principle `lt_irrefl`
for a strict order,
which says that we have `¬ a < a` for every `a`.
The asymmetry principle `lt_asymm` says that we have
`a < b → ¬ b < a`. Let's show that `lt_asymm` follows
from `lt_irrefl`.
section

```lean
example (h : a < b) : ¬b < a := by
  intro h'
  have : a < a := lt_trans h h'
  apply lt_irrefl a this
```

This example introduces a couple of new tricks.
First, when you use `have` without providing
a label,
Lean uses the name `this`,
providing a convenient way to refer back to it.
Because the proof is so short, we provide an explicit proof term.
But what you should really be paying attention to in this
proof is the result of the `intro` tactic,
which leaves a goal of `False`,
and the fact that we eventually prove `False`
by applying `lt_irrefl` to a proof of `a < a`.

Here is another example, which uses the
predicate `FnHasUb` defined in the last section,
which says that a function has an upper bound.

```lean
example (h : ∀ a, ∃ x, f x > a) : ¬FnHasUb f := by
  intro fnub
  rcases fnub with ⟨a, fnuba⟩
  rcases h a with ⟨x, hx⟩
  have : f x ≤ a := fnuba x
  linarith
```

Remember that it is often convenient to use `linarith`
when a goal follows from linear equations and
inequalities that are in the context.

See if you can prove these in a similar way:

```lean
example (h : ∀ a, ∃ x, f x < a) : ¬FnHasLb f :=
  sorry

example : ¬FnHasUb fun x ↦ x :=
  sorry
```

Mathlib offers a number of useful theorems for relating orders
and negations:

```lean
#check (not_le_of_gt : a > b → ¬a ≤ b)
#check (not_lt_of_ge : a ≥ b → ¬a < b)
#check (lt_of_not_ge : ¬a ≥ b → a < b)
#check (le_of_not_gt : ¬a > b → a ≤ b)
```

Recall the predicate `Monotone f`,
which says that `f` is nondecreasing.
Use some of the theorems just enumerated to prove the following:

```lean
example (h : Monotone f) (h' : f a < f b) : a < b := by
  sorry

example (h : a ≤ b) (h' : f b < f a) : ¬Monotone f := by
  sorry
```

We can show that the first example in the last snippet
cannot be proved if we replace `<` by `≤`.
Notice that we can prove the negation of a universally
quantified statement by giving a counterexample.
Complete the proof.

```lean
example : ¬∀ {f : ℝ → ℝ}, Monotone f → ∀ {a b}, f a ≤ f b → a ≤ b := by
  intro h
  let f := fun x : ℝ ↦ (0 : ℝ)
  have monof : Monotone f := by sorry
  have h' : f 1 ≤ f 0 := le_refl _
  sorry
```

This example introduces the `let` tactic,
which adds a _local definition_ to the context.
If you put the cursor after the `let` command,
in the goal window you will see that the definition
`f : ℝ → ℝ := fun x ↦ 0` has been added to the context.
Lean will unfold the definition of `f` when it has to.
In particular, when we prove `f 1 ≤ f 0` with `le_refl`,
Lean reduces `f 1` and `f 0` to `0`.

Use `le_of_not_gt` to prove the following:

```lean
example (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := by
  sorry
```

Implicit in many of the proofs we have just done
is the fact that if `P` is any property,
saying that there is nothing with property `P`
is the same as saying that everything fails to have
property `P`,
and saying that not everything has property `P`
is equivalent to saying that something fails to have property `P`.
In other words, all four of the following implications
are valid (but one of them cannot be proved with what we explained so
far):

```lean
variable {α : Type*} (P : α → Prop) (Q : Prop)

example (h : ¬∃ x, P x) : ∀ x, ¬P x := by
  sorry

example (h : ∀ x, ¬P x) : ¬∃ x, P x := by
  sorry

example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  sorry

example (h : ∃ x, ¬P x) : ¬∀ x, P x := by
  sorry
```

The first, second, and fourth are straightforward to
prove using the methods you have already seen.
We encourage you to try it.
The third is more difficult, however,
because it concludes that an object exists
from the fact that its nonexistence is contradictory.
This is an instance of _classical_ mathematical reasoning.
We can use proof by contradiction
to prove the third implication as follows.

```lean
example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  by_contra h'
  apply h
  intro x
  show P x
  by_contra h''
  exact h' ⟨x, h''⟩
```

Make sure you understand how this works.
The `by_contra` tactic
allows us to prove a goal `Q` by assuming `¬ Q`
and deriving a contradiction.
In fact, it is equivalent to using the
equivalence `not_not : ¬ ¬ Q ↔ Q`.
Confirm that you can prove the forward direction
of this equivalence using `by_contra`,
while the reverse direction follows from the
ordinary rules for negation.

```lean
example (h : ¬¬Q) : Q := by
  sorry

example (h : Q) : ¬¬Q := by
  sorry
```

Use proof by contradiction to establish the following,
which is the converse of one of the implications we proved above.
(Hint: use `intro` first.)

```lean
example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  sorry
```

It is often tedious to work with compound statements with
a negation in front,
and it is a common mathematical pattern to replace such
statements with equivalent forms in which the negation
has been pushed inward.
To facilitate this, Mathlib offers a `push_neg` tactic,
which restates the goal in this way.
The command `push_neg at h` restates the hypothesis `h`.

```lean
example (h : ¬∀ a, ∃ x, f x > a) : FnHasUb f := by
  push_neg at h
  exact h

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  dsimp only [FnHasUb, FnUb] at h
  push_neg at h
  exact h
```

In the second example, we use dsimp to
expand the definitions of `FnHasUb` and `FnUb`.
(We need to use `dsimp` rather than `rw`
to expand `FnUb`,
because it appears in the scope of a quantifier.)
You can verify that in the examples above
with `¬∃ x, P x` and `¬∀ x, P x`,
the `push_neg` tactic does the expected thing.
Without even knowing how to use the conjunction
symbol,
you should be able to use `push_neg`
to prove the following:

```lean
example (h : ¬Monotone f) : ∃ x y, x ≤ y ∧ f y < f x := by
  sorry
```

Mathlib also has a tactic, `contrapose`,
which transforms a goal `A → B` to `¬B → ¬A`.
Similarly, given a goal of proving `B` from
hypothesis `h : A`,
`contrapose h` leaves you with a goal of proving
`¬A` from hypothesis `¬B`.
Using `contrapose!` instead of `contrapose`
applies `push_neg` to the goal and the relevant
hypothesis as well.

```lean
example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  contrapose! h
  exact h

example (x : ℝ) (h : ∀ ε > 0, x ≤ ε) : x ≤ 0 := by
  contrapose! h
  use x / 2
  constructor <;> linarith
```

We have not yet explained the `constructor` command
or the use of the semicolon after it,
but we will do that in the next section.

We close this section with
the principle of _ex falso_,
which says that anything follows from a contradiction.
In Lean, this is represented by `False.elim`,
which establishes `False → P` for any proposition `P`.
This may seem like a strange principle,
but it comes up fairly often.
We often prove a theorem by splitting on cases,
and sometimes we can show that one of
the cases is contradictory.
In that case, we need to assert that the contradiction
establishes the goal so we can move on to the next one.
(We will see instances of reasoning by cases in
:numref:`disjunction`.)

Lean provides a number of ways of closing
a goal once a contradiction has been reached.

```lean
example (h : 0 < 0) : a > 37 := by
  exfalso
  apply lt_irrefl 0 h

example (h : 0 < 0) : a > 37 :=
  absurd h (lt_irrefl 0)

example (h : 0 < 0) : a > 37 := by
  have h' : ¬0 < 0 := lt_irrefl 0
  contradiction
```

The `exfalso` tactic replaces the current goal with
the goal of proving `False`.
Given `h : P` and `h' : ¬ P`,
the term `absurd h h'` establishes any proposition.
Finally, the `contradiction` tactic tries to close a goal
by finding a contradiction in the hypotheses,
such as a pair of the form `h : P` and `h' : ¬ P`.
Of course, in this example, `linarith` also works.

## Conjunction and Iff

You have already seen that the conjunction symbol, `∧`,
is used to express "and."
The `constructor` tactic allows you to prove a statement of
the form `A ∧ B`
by proving `A` and then proving `B`.

```lean
example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y := by
  constructor
  · assumption
  intro h
  apply h₁
  rw [h]
```

In this example, the `assumption` tactic
tells Lean to find an assumption that will solve the goal.
Notice that the final `rw` finishes the goal by
applying the reflexivity of `≤`.
The following are alternative ways of carrying out
the previous examples using the anonymous constructor
angle brackets.
The first is a slick proof-term version of the
previous proof,
which drops into tactic mode at the keyword `by`.

```lean
example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y :=
  ⟨h₀, fun h ↦ h₁ (by rw [h])⟩

example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y :=
  have h : x ≠ y := by
    contrapose! h₁
    rw [h₁]
  ⟨h₀, h⟩
```

_Using_ a conjunction instead of proving one involves unpacking the proofs of the
two parts.
You can use the `rcases` tactic for that,
as well as `rintro` or a pattern-matching `fun`,
all in a manner similar to the way they are used with
the existential quantifier.

```lean
example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  rcases h with ⟨h₀, h₁⟩
  contrapose! h₁
  exact le_antisymm h₀ h₁

example {x y : ℝ} : x ≤ y ∧ x ≠ y → ¬y ≤ x := by
  rintro ⟨h₀, h₁⟩ h'
  exact h₁ (le_antisymm h₀ h')

example {x y : ℝ} : x ≤ y ∧ x ≠ y → ¬y ≤ x :=
  fun ⟨h₀, h₁⟩ h' ↦ h₁ (le_antisymm h₀ h')
```

In analogy to the `obtain` tactic, there is also a pattern-matching `have`:

```lean
example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  have ⟨h₀, h₁⟩ := h
  contrapose! h₁
  exact le_antisymm h₀ h₁
```

In contrast to `rcases`, here the `have` tactic leaves `h` in the context.
And even though we won't use them, once again we have the computer scientists'
pattern-matching syntax:

```lean
example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  cases h
  case intro h₀ h₁ =>
    contrapose! h₁
    exact le_antisymm h₀ h₁

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  cases h
  next h₀ h₁ =>
    contrapose! h₁
    exact le_antisymm h₀ h₁

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  match h with
    | ⟨h₀, h₁⟩ =>
        contrapose! h₁
        exact le_antisymm h₀ h₁
```

In contrast to using an existential quantifier,
you can also extract proofs of the two components
of a hypothesis `h : A ∧ B`
by writing `h.left` and `h.right`,
or, equivalently, `h.1` and `h.2`.

```lean
example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  intro h'
  apply h.right
  exact le_antisymm h.left h'

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x :=
  fun h' ↦ h.right (le_antisymm h.left h')
```

Try using these techniques to come up with various ways of proving of the following:

```lean
example {m n : ℕ} (h : m ∣ n ∧ m ≠ n) : m ∣ n ∧ ¬n ∣ m :=
  sorry
```

You can nest uses of `∃` and `∧`
with anonymous constructors, `rintro`, and `rcases`.

```lean
example : ∃ x : ℝ, 2 < x ∧ x < 4 :=
  ⟨5 / 2, by norm_num, by norm_num⟩

example (x y : ℝ) : (∃ z : ℝ, x < z ∧ z < y) → x < y := by
  rintro ⟨z, xltz, zlty⟩
  exact lt_trans xltz zlty

example (x y : ℝ) : (∃ z : ℝ, x < z ∧ z < y) → x < y :=
  fun ⟨z, xltz, zlty⟩ ↦ lt_trans xltz zlty
```

You can also use the `use` tactic:

```lean
example : ∃ x : ℝ, 2 < x ∧ x < 4 := by
  use 5 / 2
  constructor <;> norm_num

example : ∃ m n : ℕ, 4 < m ∧ m < n ∧ n < 10 ∧ Nat.Prime m ∧ Nat.Prime n := by
  use 5
  use 7
  norm_num

example {x y : ℝ} : x ≤ y ∧ x ≠ y → x ≤ y ∧ ¬y ≤ x := by
  rintro ⟨h₀, h₁⟩
  use h₀
  exact fun h' ↦ h₁ (le_antisymm h₀ h')
```

In the first example, the semicolon after the `constructor` command tells Lean to use the
`norm_num` tactic on both of the goals that result.

In Lean, `A ↔ B` is _not_ defined to be `(A → B) ∧ (B → A)`,
but it could have been,
and it behaves roughly the same way.
You have already seen that you can write `h.mp` and `h.mpr`
or `h.1` and `h.2` for the two directions of `h : A ↔ B`.
You can also use `cases` and friends.
To prove an if-and-only-if statement,
you can use `constructor` or angle brackets,
just as you would if you were proving a conjunction.

```lean
example {x y : ℝ} (h : x ≤ y) : ¬y ≤ x ↔ x ≠ y := by
  constructor
  · contrapose!
    rintro rfl
    rfl
  contrapose!
  exact le_antisymm h

example {x y : ℝ} (h : x ≤ y) : ¬y ≤ x ↔ x ≠ y :=
  ⟨fun h₀ h₁ ↦ h₀ (by rw [h₁]), fun h₀ h₁ ↦ h₀ (le_antisymm h h₁)⟩
```

The last proof term is inscrutable. Remember that you can
use underscores while writing an expression like that to
see what Lean expects.

Try out the various techniques and gadgets you have just seen
in order to prove the following:

```lean
example {x y : ℝ} : x ≤ y ∧ ¬y ≤ x ↔ x ≤ y ∧ x ≠ y :=
  sorry
```

For a more interesting exercise, show that for any
two real numbers `x` and `y`,
`x^2 + y^2 = 0` if and only if `x = 0` and `y = 0`.
We suggest proving an auxiliary lemma using
`linarith`, `pow_two_nonneg`, and `pow_eq_zero`.

```lean
theorem aux {x y : ℝ} (h : x ^ 2 + y ^ 2 = 0) : x = 0 :=
  have h' : x ^ 2 = 0 := by sorry
  pow_eq_zero h'

example (x y : ℝ) : x ^ 2 + y ^ 2 = 0 ↔ x = 0 ∧ y = 0 :=
  sorry
```

In Lean, bi-implication leads a double-life.
You can treat it like a conjunction and use its two
parts separately.
But Lean also knows that it is a reflexive, symmetric,
and transitive relation between propositions,
and you can also use it with `calc` and `rw`.
It is often convenient to rewrite a statement to
an equivalent one.
In the next example, we use `abs_lt` to
replace an expression of the form `|x| < y`
by the equivalent expression `- y < x ∧ x < y`,
and in the one after that we use `Nat.dvd_gcd_iff`
to replace an expression of the form `m ∣ Nat.gcd n k` by the equivalent expression `m ∣ n ∧ m ∣ k`.

```lean
example (x : ℝ) : |x + 3| < 5 → -8 < x ∧ x < 2 := by
  rw [abs_lt]
  intro h
  constructor <;> linarith

example : 3 ∣ Nat.gcd 6 15 := by
  rw [Nat.dvd_gcd_iff]
  constructor <;> norm_num
```

See if you can use `rw` with the theorem below
to provide a short proof that negation is not a
nondecreasing function. (Note that `push_neg` won't
unfold definitions for you, so the `rw [Monotone]` in
the proof of the theorem is needed.)

```lean
theorem not_monotone_iff {f : ℝ → ℝ} : ¬Monotone f ↔ ∃ x y, x ≤ y ∧ f x > f y := by
  rw [Monotone]
  push_neg
  rfl

example : ¬Monotone fun x : ℝ ↦ -x := by
  sorry
```

The remaining exercises in this section are designed
to give you some more practice with conjunction and
bi-implication. Remember that a _partial order_ is a
binary relation that is transitive, reflexive, and
antisymmetric.
An even weaker notion sometimes arises:
a _preorder_ is just a reflexive, transitive relation.
For any pre-order `≤`,
Lean axiomatizes the associated strict pre-order by
`a < b ↔ a ≤ b ∧ ¬ b ≤ a`.
Show that if `≤` is a partial order,
then `a < b` is equivalent to `a ≤ b ∧ a ≠ b`:

```lean
variable {α : Type*} [PartialOrder α]
variable (a b : α)

example : a < b ↔ a ≤ b ∧ a ≠ b := by
  rw [lt_iff_le_not_le]
  sorry
```

Beyond logical operations, you do not need
anything more than `le_refl` and `le_trans`.
Show that even in the case where `≤`
is only assumed to be a preorder,
we can prove that the strict order is irreflexive
and transitive.
In the second example,
for convenience, we use the simplifier rather than `rw`
to express `<` in terms of `≤` and `¬`.
We will come back to the simplifier later,
but here we are only relying on the fact that it will
use the indicated lemma repeatedly, even if it needs
to be instantiated to different values.

```lean
variable {α : Type*} [Preorder α]
variable (a b c : α)

-- EXAMPLES:
example : ¬a < a := by
  rw [lt_iff_le_not_le]
  sorry

example : a < b → b < c → a < c := by
  simp only [lt_iff_le_not_le]
  sorry
```

## Disjunction

The canonical way to prove a disjunction `A ∨ B` is to prove
`A` or to prove `B`.
The `left` tactic chooses `A`,
and the `right` tactic chooses `B`.

```lean
variable {x y : ℝ}

example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  left
  linarith [pow_two_nonneg x]

example (h : -y > x ^ 2 + 1) : y > 0 ∨ y < -1 := by
  right
  linarith [pow_two_nonneg x]
```

We cannot use an anonymous constructor to construct a proof
of an "or" because Lean would have to guess
which disjunct we are trying to prove.
When we write proof terms we can use
`Or.inl` and `Or.inr` instead
to make the choice explicitly.
Here, `inl` is short for "introduction left" and
`inr` is short for "introduction right."

```lean
example (h : y > 0) : y > 0 ∨ y < -1 :=
  Or.inl h

example (h : y < -1) : y > 0 ∨ y < -1 :=
  Or.inr h
```

It may seem strange to prove a disjunction by proving one side
or the other.
In practice, which case holds usually depends on a case distinction
that is implicit or explicit in the assumptions and the data.
The `rcases` tactic allows us to make use of a hypothesis
of the form `A ∨ B`.
In contrast to the use of `rcases` with conjunction or an
existential quantifier,
here the `rcases` tactic produces _two_ goals.
Both have the same conclusion, but in the first case,
`A` is assumed to be true,
and in the second case,
`B` is assumed to be true.
In other words, as the name suggests,
the `rcases` tactic carries out a proof by cases.
As usual, we can tell Lean what names to use for the hypotheses.
In the next example, we tell Lean
to use the name `h` on each branch.

```lean
example : x < |y| → x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    intro h; left; exact h
  . rw [abs_of_neg h]
    intro h; right; exact h
```

Notice that the pattern changes from `⟨h₀, h₁⟩` in the case of
a conjunction to `h₀ | h₁` in the case of a disjunction.
Think of the first pattern as matching against data the contains
_both_ an `h₀` and a `h₁`, whereas second pattern, with the bar,
matches against data that contains _either_ an `h₀` or `h₁`.
In this case, because the two goals are separate, we have chosen
to use the same name, `h`, in each case.

The absolute value function is defined in such a way
that we can immediately prove that
`x ≥ 0` implies `|x| = x`
(this is the theorem `abs_of_nonneg`)
and `x < 0` implies `|x| = -x` (this is `abs_of_neg`).
The expression `le_or_gt 0 x` establishes `0 ≤ x ∨ x < 0`,
allowing us to split on those two cases.

Lean also supports the computer scientists' pattern-matching
syntax for disjunction. Now the `cases` tactic is more attractive,
because it allows us to name each `case`, and name the hypothesis
that is introduced closer to where it is used.

```lean
example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  case inl h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  case inr h =>
    rw [abs_of_neg h]
    intro h; right; exact h
```

The names `inl` and `inr` are short for "intro left" and "intro right,"
respectively. Using `case` has the advantage that you can prove the
cases in either order; Lean uses the tag to find the relevant goal.
If you don't care about that, you can use `next`, or `match`,
or even a pattern-matching `have`.

```lean
example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  next h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  next h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  match le_or_gt 0 y with
    | Or.inl h =>
      rw [abs_of_nonneg h]
      intro h; left; exact h
    | Or.inr h =>
      rw [abs_of_neg h]
      intro h; right; exact h
```

In the case of `match`, we need to use the full names
`Or.inl` and `Or.inr` of the canonical ways to prove a disjunction.
In this textbook, we will generally use `rcases` to split on the
cases of a disjunction.

Try proving the triangle inequality using the
first two theorems in the next snippet.
They are given the same names they have in Mathlib.

```lean
namespace MyAbs

theorem le_abs_self (x : ℝ) : x ≤ |x| := by
  sorry

theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
  sorry

theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  sorry
```

In case you enjoyed these (pun intended) and
you want more practice with disjunction,
try these.

```lean
theorem lt_abs : x < |y| ↔ x < y ∨ x < -y := by
  sorry

theorem abs_lt : |x| < y ↔ -y < x ∧ x < y := by
  sorry
```

You can also use `rcases` and `rintro` with nested disjunctions.
When these result in a genuine case split with multiple goals,
the patterns for each new goal are separated by a vertical bar.

```lean
example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · left
    exact xlt
  · contradiction
  . right; exact xgt
```

You can still nest patterns and use the `rfl` keyword
to substitute equations:

```lean
example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [mul_assoc]
    apply dvd_mul_right
  . rw [mul_comm, mul_assoc]
    apply dvd_mul_right
```

See if you can prove the following with a single (long) line.
Use `rcases` to unpack the hypotheses and split on cases,
and use a semicolon and `linarith` to solve each branch.

```lean
example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  sorry
```

On the real numbers, an equation `x * y = 0`
tells us that `x = 0` or `y = 0`.
In Mathlib, this fact is known as `eq_zero_or_eq_zero_of_mul_eq_zero`,
and it is another nice example of how a disjunction can arise.
See if you can use it to prove the following:

```lean
example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  sorry

example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  sorry
```

Remember that you can use the `ring` tactic to help
with calculations.

In an arbitrary ring :math:`R`, an element :math:`x` such
that :math:`x y = 0` for some nonzero :math:`y` is called
a _left zero divisor_,
an element :math:`x` such
that :math:`y x = 0` for some nonzero :math:`y` is called
a _right zero divisor_,
and an element that is either a left or right zero divisor
is called simply a _zero divisor_.
The theorem `eq_zero_or_eq_zero_of_mul_eq_zero`
says that the real numbers have no nontrivial zero divisors.
A commutative ring with this property is called an _integral domain_.
Your proofs of the two theorems above should work equally well
in any integral domain:

```lean
variable {R : Type*} [CommRing R] [IsDomain R]
variable (x y : R)

example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  sorry

example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  sorry
```

In fact, if you are careful, you can prove the first
theorem without using commutativity of multiplication.
In that case, it suffices to assume that `R` is
a `Ring` instead of an `CommRing`.

.. index:: excluded middle

Sometimes in a proof we want to split on cases
depending on whether some statement is true or not.
For any proposition `P`, we can use
`em P : P ∨ ¬ P`.
The name `em` is short for "excluded middle."

```lean
example (P : Prop) : ¬¬P → P := by
  intro h
  cases em P
  · assumption
  . contradiction
```

Alternatively, you can use the `by_cases` tactic.

```lean
-- EXAMPLES:
example (P : Prop) : ¬¬P → P := by
  intro h
  by_cases h' : P
  · assumption
  contradiction
```

Notice that the `by_cases` tactic lets you
specify a label for the hypothesis that is
introduced in each branch,
in this case, `h' : P` in one and `h' : ¬ P`
in the other.
If you leave out the label,
Lean uses `h` by default.
Try proving the following equivalence,
using `by_cases` to establish one direction.

```lean
example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
  sorry
```

## Sequences and Convergence

We now have enough skills at our disposal to do some real mathematics.
In Lean, we can represent a sequence $s_0, s_1, s_2, \ldots$ of
real numbers as a function `s : ℕ → ℝ`.
Such a sequence is said to _converge_ to a number :math:`a` if for every
$\varepsilon > 0$ there is a point beyond which the sequence
remains within $\varepsilon$ of $a$,
that is, there is a number $N$ such that for every
$n \ge N$, $| s_n - a | < \varepsilon$.
In Lean, we can render this as follows:

```lean
def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε
```

The notation `∀ ε > 0, ...` is a convenient abbreviation
for `∀ ε, ε > 0 → ...`, and, similarly,
`∀ n ≥ N, ...` abbreviates `∀ n, n ≥ N →  ...`.
And remember that `ε > 0`, in turn, is defined as `0 < ε`,
and `n ≥ N` is defined as `N ≤ n`.

.. index:: extensionality, ext, tactics ; ext

In this section, we'll establish some properties of convergence.
But first, we will discuss three tactics for working with equality
that will prove useful.
The first, the `ext` tactic,
gives us a way of proving that two functions are equal.
Let $f(x) = x + 1$ and $g(x) = 1 + x$
be functions from reals to reals.
Then, of course, $f = g$, because they return the same
value for every $x$.
The `ext` tactic enables us to prove an equation between functions
by proving that their values are the same
at all the values of their arguments.

```lean
example : (fun x y : ℝ ↦ (x + y) ^ 2) = fun x y : ℝ ↦ x ^ 2 + 2 * x * y + y ^ 2 := by
  ext
  ring
```

.. index:: congr, tactics ; congr

We'll see later that `ext` is actually more general, and also one can
specify the name of the variables that appear.
For instance you can try to replace `ext` with `ext u v` in the
above proof.
The second tactic, the `congr` tactic,
allows us to prove an equation between two expressions
by reconciling the parts that are different:

```lean
example (a b : ℝ) : |a| = |a - b + b| := by
  congr
  ring
```

Here the `congr` tactic peels off the `abs` on each side,
leaving us to prove `a = a - b + b`.

.. index:: convert, tactics ; convert

Finally, the `convert` tactic is used to apply a theorem
to a goal when the conclusion of the theorem doesn't quite match.
For example, suppose we want to prove `a < a * a` from `1 < a`.
A theorem in the library, `mul_lt_mul_right`,
will let us prove `1 * a < a * a`.
One possibility is to work backwards and rewrite the goal
so that it has that form.
Instead, the `convert` tactic lets us apply the theorem
as it is,
and leaves us with the task of proving the equations that
are needed to make the goal match.

```lean
example {a : ℝ} (h : 1 < a) : a < a * a := by
  convert (mul_lt_mul_right _).2 h
  · rw [one_mul]
  exact lt_trans zero_lt_one h
```

This example illustrates another useful trick: when we apply an
expression with an underscore
and Lean can't fill it in for us automatically,
it simply leaves it for us as another goal.

The following shows that any constant sequence $a, a, a, \ldots$
converges.

```lean
theorem convergesTo_const (a : ℝ) : ConvergesTo (fun x : ℕ ↦ a) a := by
  intro ε εpos
  use 0
  intro n nge
  rw [sub_self, abs_zero]
  apply εpos
```

Lean has a tactic, `simp`, which can often save you the
trouble of carrying out steps like `rw [sub_self, abs_zero]`
by hand.
We will tell you more about it soon.

For a more interesting theorem, let's show that if `s`
converges to `a` and `t` converges to `b`, then
`fun n ↦ s n + t n` converges to `a + b`.
It is helpful to have a clear pen-and-paper
proof in mind before you start writing a formal one.
Given `ε` greater than `0`,
the idea is to use the hypotheses to obtain an `Ns`
such that beyond that point, `s` is within `ε / 2`
of `a`,
and an `Nt` such that beyond that point, `t` is within
`ε / 2` of `b`.
Then, whenever `n` is greater than or equal to the
maximum of `Ns` and `Nt`,
the sequence `fun n ↦ s n + t n` should be within `ε`
of `a + b`.
The following example begins to implement this strategy.
See if you can finish it off.

```lean
theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n + t n) (a + b) := by
  intro ε εpos
  dsimp -- this line is not needed but cleans up the goal a bit.
  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
  rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
  use max Ns Nt
  sorry
```

As hints, you can use `le_of_max_le_left` and `le_of_max_le_right`,
and `norm_num` can prove `ε / 2 + ε / 2 = ε`.
Also, it is helpful to use the `congr` tactic to
show that `|s n + t n - (a + b)|` is equal to
`|(s n - a) + (t n - b)|,`
since then you can use the triangle inequality.
Notice that we marked all the variables `s`, `t`, `a`, and `b`
implicit because they can be inferred from the hypotheses.

Proving the same theorem with multiplication in place
of addition is tricky.
We will get there by proving some auxiliary statements first.
See if you can also finish off the next proof,
which shows that if `s` converges to `a`,
then `fun n ↦ c * s n` converges to `c * a`.
It is helpful to split into cases depending on whether `c`
is equal to zero or not.
We have taken care of the zero case,
and we have left you to prove the result with
the extra assumption that `c` is nonzero.

```lean
theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by
  by_cases h : c = 0
  · convert convergesTo_const 0
    · rw [h]
      ring
    rw [h]
    ring
  have acpos : 0 < |c| := abs_pos.mpr h
  sorry
```

The next theorem is also independently interesting:
it shows that a convergent sequence is eventually bounded
in absolute value.
We have started you off; see if you can finish it.

```lean
theorem exists_abs_le_of_convergesTo {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
    ∃ N b, ∀ n, N ≤ n → |s n| < b := by
  rcases cs 1 zero_lt_one with ⟨N, h⟩
  use N, |a| + 1
  sorry
```

In fact, the theorem could be strengthened to assert
that there is a bound `b` that holds for all values of `n`.
But this version is strong enough for our purposes,
and we will see at the end of this section that it
holds more generally.

The next lemma is auxiliary: we prove that if
`s` converges to `a` and `t` converges to `0`,
then `fun n ↦ s n * t n` converges to `0`.
To do so, we use the previous theorem to find a `B`
that bounds `s` beyond some point `N₀`.
See if you can understand the strategy we have outlined
and finish the proof.

```lean
theorem aux {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
    ConvergesTo (fun n ↦ s n * t n) 0 := by
  intro ε εpos
  dsimp
  rcases exists_abs_le_of_convergesTo cs with ⟨N₀, B, h₀⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
  have pos₀ : ε / B > 0 := div_pos εpos Bpos
  rcases ct _ pos₀ with ⟨N₁, h₁⟩
  sorry
```

If you have made it this far, congratulations!
We are now within striking distance of our theorem.
The following proof finishes it off.

```lean
-- BOTH:
theorem convergesTo_mul {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n * t n) (a * b) := by
  have h₁ : ConvergesTo (fun n ↦ s n * (t n + -b)) 0 := by
    apply aux cs
    convert convergesTo_add ct (convergesTo_const (-b))
    ring
  have := convergesTo_add h₁ (convergesTo_mul_const b cs)
  convert convergesTo_add h₁ (convergesTo_mul_const b cs) using 1
  · ext; ring
  ring
```

For another challenging exercise,
try filling out the following sketch of a proof that limits
are unique.
(If you are feeling bold,
you can delete the proof sketch and try proving it from scratch.)

```lean
theorem convergesTo_unique {s : ℕ → ℝ} {a b : ℝ}
      (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
    a = b := by
  by_contra abne
  have : |a - b| > 0 := by sorry
  let ε := |a - b| / 2
  have εpos : ε > 0 := by
    change |a - b| / 2 > 0
    linarith
  rcases sa ε εpos with ⟨Na, hNa⟩
  rcases sb ε εpos with ⟨Nb, hNb⟩
  let N := max Na Nb
  have absa : |s N - a| < ε := by sorry
  have absb : |s N - b| < ε := by sorry
  have : |a - b| < |a - b| := by sorry
  exact lt_irrefl _ this
```

We close the section with the observation that our proofs can be generalized.
For example, the only properties that we have used of the
natural numbers is that their structure carries a partial order
with `min` and `max`.
You can check that everything still works if you replace `ℕ`
everywhere by any linear order `α`:

```lean
variable {α : Type*} [LinearOrder α]

def ConvergesTo' (s : α → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε
```

In :numref:`filters`, we will see that Mathlib has mechanisms
for dealing with convergence in vastly more general terms,
not only abstracting away particular features of the domain
and codomain,
but also abstracting over different types of convergence.
