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
