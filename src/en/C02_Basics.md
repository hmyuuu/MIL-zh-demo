# Basics

This chapter is designed to introduce you to the nuts and
bolts of mathematical reasoning in Lean: calculating,
applying lemmas and theorems,
and reasoning about generic structures.

## Calculating

We generally learn to carry out mathematical calculations
without thinking of them as proofs.
But when we justify each step in a calculation,
as Lean requires us to do,
the net result is a proof that the left-hand side of the calculation
is equal to the right-hand side.

In Lean, stating a theorem is tantamount to stating a goal,
namely, the goal of proving the theorem.
Lean provides the rewriting tactic `rw`,
to replace the left-hand side of an identity by the right-hand side
in the goal. If `a`, `b`, and `c` are real numbers,
`mul_assoc a b c` is the identity `a * b * c = a * (b * c)`
and `mul_comm a b` is the identity `a * b = b * a`.
Lean provides automation that generally eliminates the need
to refer the facts like these explicitly,
but they are useful for the purposes of illustration.
In Lean, multiplication associates to the left,
so the left-hand side of `mul_assoc` could also be written `(a * b) * c`.
However, it is generally good style to be mindful of Lean's
notational conventions and leave out parentheses when Lean does as well.

Let's try out `rw`.

```lean
example (a b c : ℝ) : a * b * c = b * (a * c) := by
  rw [mul_comm a b]
  rw [mul_assoc b a c]
```

The `import` lines at the beginning of the associated examples file
import the theory of the real numbers from Mathlib, as well as useful automation.
For the sake of brevity,
we generally suppress information like this in the textbook.

You are welcome to make changes to see what happens.
You can type the `ℝ` character as `\R` or `\real`
in VS Code.
The symbol doesn't appear until you hit space or the tab key.
If you hover over a symbol when reading a Lean file,
VS Code will show you the syntax that can be used to enter it.
If you are curious to see all available abbreviations, you can hit Ctrl-Shift-P
and then type abbreviations to get access to the `Lean 4: Show all abbreviations` command.
If your keyboard does not have an easily accessible backslash,
you can change the leading character by changing the
`lean4.input.leader` setting.

When a cursor is in the middle of a tactic proof,
Lean reports on the current _proof state_ in the
_Lean Infoview_ window.
As you move your cursor past each step of the proof,
you can see the state change.
A typical proof state in Lean might look as follows:

```lean
1 goal
x y : ℕ,
h₁ : Prime x,
h₂ : ¬Even x,
h₃ : y > x
⊢ y ≥ 4
```

The lines before the one* that begins with `⊢` denote the \_context*:
they are the objects and assumptions currently at play.
In this example, these include two objects, `x` and `y`,
each a natural number.
They also include three assumptions,
labelled `h₁`, `h₂`, and `h₃`.
In Lean, everything in a context is labelled with an identifier.
You can type these subscripted labels as `h\1`, `h\2`, and `h\3`,
but any legal identifiers would do:
you can use `h1`, `h2`, `h3` instead,
or `foo`, `bar`, and `baz`.
The last line represents the _goal_,
that is, the fact to be proved.
Sometimes people use _target_ for the fact to be proved,
and _goal_ for the combination of the context and the target.
In practice, the intended meaning is usually clear.

Try proving these identities,
in each case replacing `sorry` by a tactic proof.
With the `rw` tactic, you can use a left arrow (`\l`)
to reverse an identity.
For example, `rw [← mul_assoc a b c]`
replaces `a * (b * c)` by `a * b * c` in the current goal. Note that
the left-pointing arrow refers to going from right to left in the identity provided
by `mul_assoc`, it has nothing to do with the left or right side of the goal.

```lean
example (a b c : ℝ) : c * b * a = b * (a * c) := by
  sorry

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  sorry
```

You can also use identities like `mul_assoc` and `mul_comm` without arguments.
In this case, the rewrite tactic tries to match the left-hand side with
an expression in the goal,
using the first pattern it finds.

```lean
example (a b c : ℝ) : a * b * c = b * c * a := by
  rw [mul_assoc]
  rw [mul_comm]
```

You can also provide _partial_ information.
For example, `mul_comm a` matches any pattern of the form
`a * ?` and rewrites it to `? * a`.
Try doing the first of these examples without
providing any arguments at all,
and the second with only one argument.

```lean
example (a b c : ℝ) : a * (b * c) = b * (c * a) := by
  sorry

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  sorry
```

You can also use `rw` with facts from the local context.

```lean
example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h']
  rw [← mul_assoc]
  rw [h]
  rw [mul_assoc]
```

Try these, using the theorem `sub_self` for the second one:

```lean
example (a b c d e f : ℝ) (h : b * c = e * f) : a * b * c * d = a * e * f * d := by
  sorry

example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by
  sorry
```

Multiple rewrite commands can be carried out with a single command,
by listing the relevant identities separated by commas inside the square brackets.

```lean
example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h', ← mul_assoc, h, mul_assoc]
```

You still see the incremental progress by placing the cursor after
a comma in any list of rewrites.

Another trick is that we can declare variables once and for all outside
an example or theorem. Lean then includes them automatically.

```lean
variable (a b c d e f : ℝ)

example (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h', ← mul_assoc, h, mul_assoc]

```

Inspection of the tactic state at the beginning of the above proof
reveals that Lean indeed included all variables.
We can delimit the scope of the declaration by putting it
in a `section ... end` block.
Finally, recall from the introduction that Lean provides us with a
command to determine the type of an expression:

```lean
section
variable (a b c : ℝ)

#check a
#check a + b
#check (a : ℝ)
#check mul_comm a b
#check (mul_comm a b : a * b = b * a)
#check mul_assoc c a b
#check mul_comm a
#check mul_comm

end
```

The `#check` command works for both objects and facts.
In response to the command `#check a`, Lean reports that `a` has type `ℝ`.
In response to the command `#check mul_comm a b`,
Lean reports that `mul_comm a b` is a proof of the fact `a * b = b * a`.
The command `#check (a : ℝ)` states our expectation that the
type of `a` is `ℝ`,
and Lean will raise an error if that is not the case.
We will explain the output of the last three `#check` commands later,
but in the meanwhile, you can take a look at them,
and experiment with some `#check` commands of your own.

Let's try some more examples. The theorem `two_mul a` says
that `2 * a = a + a`. The theorems `add_mul` and `mul_add`
express the distributivity of multiplication over addition,
and the theorem `add_assoc` expresses the associativity of addition.
Use the `#check` command to see the precise statements.

```lean
example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  rw [mul_add, add_mul, add_mul]
  rw [← add_assoc, add_assoc (a * a)]
  rw [mul_comm b a, ← two_mul]
```

Whereas it is possible to figure out what it going on in this proof
by stepping through it in the editor,
it is hard to read on its own.
Lean provides a more structured way of writing proofs like this
using the `calc` keyword.

```lean
example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      rw [mul_add, add_mul, add_mul]
    * = a * a + (b * a + a * b) + b * b := by
      rw [← add_assoc, add_assoc (a * a)]
    * = a * a + 2 * (a * b) + b * b := by
      rw [mul_comm b a, ← two_mul]
```

Notice that the proof does _not_ begin with `by`:
an expression that begins with `calc` is a _proof term_.
A `calc` expression can also be used inside a tactic proof,
but Lean interprets it as the instruction to use the resulting
proof term to solve the goal.
The `calc` syntax is finicky: the underscores and justification
have to be in the format indicated above.
Lean uses indentation to determine things like where a block
of tactics or a `calc` block begins and ends;
try changing the indentation in the proof above to see what happens.

one way to write a `calc` proof is to outline it first
using the `sorry` tactic for justification,
make sure Lean accepts the expression modulo these,
and then justify the individual steps using tactics.

```lean
example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      sorry
    * = a * a + (b * a + a * b) + b * b := by
      sorry
    * = a * a + 2 * (a * b) + b * b := by
      sorry
```

Try proving the following identity using both a pure `rw` proof
and a more structured `calc` proof:

```lean
example : (a + b) * (c + d) = a * c + a * d + b * c + b * d := by
  sorry
```

The following exercise is a little more challenging.
You can use the theorems listed underneath.

```lean
example (a b : ℝ) : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  sorry

#check pow_two a
#check mul_sub a b c
#check add_mul a b c
#check add_sub a b c
#check sub_sub a b c
#check add_zero a
```

We can also perform rewriting in an assumption in the context.
For example, `rw [mul_comm a b] at hyp` replaces `a * b` by `b * a`
in the assumption `hyp`.

```lean
example (a b c d : ℝ) (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp'] at hyp
  rw [mul_comm d a] at hyp
  rw [← two_mul (a * d)] at hyp
  rw [← mul_assoc 2 a d] at hyp
  exact hyp
```

In the last step, the `exact` tactic can use `hyp` to solve the goal
because at that point `hyp` matches the goal exactly.

We close this section by noting that Mathlib provides a
useful bit of automation with a `ring` tactic,
which is designed to prove identities in any commutative ring as long as they follow
purely from the ring axioms, without using any local assumption.
ring

```lean
example : c * b * a = b * (a * c) := by
  ring
example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  ring

example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  ring

example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp']
  ring
```

The `ring` tactic is imported indirectly when we
import `Mathlib.Data.Real.Basic`,
but we will see in the next section that it can be used
for calculations on structures other than the real numbers.
It can be imported explicitly with the command
`import Mathlib.Tactic`.
We will see there are similar tactics for other common kind of algebraic
structures.

There is a variation of `rw` called `nth_rw` that allows you to replace only particular instances of an expression in the goal.
Possible matches are enumerated starting with 1,
so in the following example, `nth_rw 2 [h]` replaces the second
occurrence of `a + b` with `c`.

```lean
example (a b c : ℕ) (h : a + b = c) : (a + b) * (a + b) = a * c + b * c := by
  nth_rw 2 [h]
  rw [add_mul]
```

## Proving Identities in Algebraic Structures

Mathematically, a ring consists of a collection of objects,
$R$, operations $+$ $\times$, and constants $0$
and $1$, and an operation $x \to -x$ such that:

- $R$ with $+$ is an _abelian group_, with $0$
  as the additive identity and negation as inverse.

- Multiplication is associative with identity $1$,
  and multiplication distributes over addition.

In Lean, the collection of objects is represented as a _type_, `R`.
The ring axioms are as follows:

```lean
variable (R : Type *) [Ring R]

#check (add_assoc : ∀ a b c : R, a + b + c = a + (b + c))
#check (add_comm : ∀ a b : R, a + b = b + a)
#check (zero_add : ∀ a : R, 0 + a = a)
#check (add_left_neg : ∀ a : R, -a + a = 0)
#check (mul_assoc : ∀ a b c : R, a * b * c = a * (b * c))
#check (mul_one : ∀ a : R, a * 1 = a)
#check (one_mul : ∀ a : R, 1 * a = a)
#check (mul_add : ∀ a b c : R, a * (b + c) = a * b + a * c)
#check (add_mul : ∀ a b c : R, (a + b) * c = a * c + b * c)
```

You will learn more about the square brackets in the first line later,
but for the time being,
suffice it to say that the declaration gives us a type, `R`,
and a ring structure on `R`.
Lean then allows us to use generic ring notation with elements of `R`,
and to make use of a library of theorems about rings.

The names of some of the theorems should look familiar:
they are exactly the ones we used to calculate with the real numbers
in the last section.
Lean is good not only for proving things about concrete mathematical
structures like the natural numbers and the integers,
but also for proving things about abstract structures,
characterized axiomatically, like rings.
Moreover, Lean supports _generic reasoning_ about
both abstract and concrete structures,
and can be trained to recognize appropriate instances.
So any theorem about rings can be applied to concrete rings
like the integers, `ℤ`, the rational numbers, `ℚ`,
and the complex numbers `ℂ`.
It can also be applied to any instance of an abstract
structure that extends rings,
such as any ordered ring or any field.

Not all important properties of the real numbers hold in an
arbitrary ring, however.
For example, multiplication on the real numbers
is commutative,
but that does not hold in general.
If you have taken a course in linear algebra,
you will recognize that, for every $n$,
the $n$ by $n$ matrices of real numbers
form a ring in which commutativity usually fails. If we declare `R` to be a
_commutative_ ring, in fact, all the theorems
in the last section continue to hold when we replace
`ℝ` by `R`.

```lean
variable (R : Type*) [CommRing R]
variable (a b c d : R)

example : c * b * a = b * (a * c) := by ring

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by ring

example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by ring

example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp']
  ring
```

We leave it to you to check that all the other proofs go through unchanged.
Notice that when a proof is short, like `by ring` or `by linarith`
or `by sorry`,
it is common (and permissible) to put it on the same line as
the `by`.
Good proof-writing style should strike a balance between concision and readability.

The goal of this section is to strengthen the skills
you have developed in the last section
and apply them to reasoning axiomatically about rings.
We will start with the axioms listed above,
and use them to derive other facts.
Most of the facts we prove are already in Mathlib.
We will give the versions we prove the same names
to help you learn the contents of the library
as well as the naming conventions.

Lean provides an organizational mechanism similar
to those used in programming languages:
when a definition or theorem `foo` is introduced in a _namespace_
`bar`, its full name is `bar.foo`.
The command `open bar` later _opens_ the namespace,
which allows us to use the shorter name `foo`.
To avoid errors due to name clashes,
in the next example we put our versions of the library
theorems in a new namespace called `MyRing.`

The next example shows that we do not need `add_zero` or `add_right_neg`
as ring axioms, because they follow from the other axioms.

```lean
namespace MyRing
variable {R : Type*} [Ring R]

theorem add_zero (a : R) : a + 0 = a := by rw [add_comm, zero_add]

theorem add_right_neg (a : R) : a + -a = 0 := by rw [add_comm, add_left_neg]

#check MyRing.add_zero
#check add_zero

end MyRing
```

The net effect is that we can temporarily reprove a theorem in the library,
and then go on using the library version after that.
But don't cheat!
In the exercises that follow, take care to use only the
general facts about rings that we have proved earlier in this section.

(If you are paying careful attention, you may have noticed that we
changed the round brackets in `(R : Type*)` for
curly brackets in `{R : Type*}`.
This declares `R` to be an _implicit argument_.
We will explain what this means in a moment,
but don't worry about it in the meanwhile.)

Here is a useful theorem:

```lean
theorem neg_add_cancel_left (a b : R) : -a + (a + b) = b := by
  rw [← add_assoc, add_left_neg, zero_add]
```

Prove the companion version:

```lean
theorem add_neg\*cancel\*right (a b : R) : a + b + -b = a := by
  sorry
```

Use these to prove the following:

```lean
theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c := by
  sorry

theorem add_right_cancel {a b c : R} (h : a + b = c + b) : a = c := by
  sorry
```

With enough planning, you can do each of them with three rewrites.

We will now explain the use of the curly braces.
Imagine you are in a situation where you have `a`, `b`, and `c`
in your context,
as well as a hypothesis `h : a + b = a + c`,
and you would like to draw the conclusion `b = c`.
In Lean, you can apply a theorem to hypotheses and facts just
the same way that you can apply them to objects,
so you might think that `add_left_cancel a b c h` is a
proof of the fact `b = c`.
But notice that explicitly writing `a`, `b`, and `c`
is redundant, because the hypothesis `h` makes it clear that
those are the objects we have in mind.
In this case, typing a few extra characters is not onerous,
but if we wanted to apply `add_left_cancel` to more complicated expressions,
writing them would be tedious.
In cases like these,
Lean allows us to mark arguments as _implicit_,
meaning that they are supposed to be left out and inferred by other means,
such as later arguments and hypotheses.
The curly brackets in`{a b c : R}`do exactly that.
So, given the statement of the theorem above,
the correct expression is simply`add_left_cancel h`.

To illustrate, let us show that `a * 0 = 0`
follows from the ring axioms.

```lean
theorem mul_zero (a : R) : a * 0 = 0 := by
have h : a * 0 + a * 0 = a * 0 + 0 := by
rw [← mul_add, add_zero, add_zero]
rw [add_left_cancel h]
```

We have used a new trick!
If you step through the proof,
you can see what is going on.
The `have` tactic introduces a new goal,
`a * 0 + a * 0 = a * 0 + 0`,
with the same context as the original goal.
The fact that the next line is indented indicates that Lean
is expecting a block of tactics that serves to prove this
new goal.
The indentation therefore promotes a modular style of proof:
the indented subproof establishes the goal
that was introduced by the `have`.
After that, we are back to proving the original goal,
except a new hypothesis `h` has been added:
having proved it, we are now free to use it.
At this point, the goal is exactly the result of `add_left_cancel h`.

We could equally well have closed the proof with
`apply add_left_cancel h` or `exact add_left_cancel h`.
The `exact` tactic takes as argument a proof term which completely proves the
current goal, without creating any new goal. The `apply` tactic is a variant
whose argument is not necessarily a complete proof. The missing pieces are either
inferred automatically by Lean or become new goals to prove.
While the `exact` tactic is technically redundant since it is strictly less powerful
than `apply`, it makes proof scripts slightly clearer to
human readers and easier to maintain when the library evolves.

Remember that multiplication is not assumed to be commutative,
so the following theorem also requires some work.

```lean
theorem zero_mul (a : R) : 0 * a = 0 := by
  sorry
```

By now, you should also be able replace each `sorry` in the next
exercise with a proof,
still using only facts about rings that we have
established in this section.

```lean
theorem neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) : -a = b := by
  sorry

theorem eq_neg_of_add_eqzero {a b : R} (h : a + b = 0) : a = -b := by
  sorry

theorem neg_zero : (-0 : R) = 0 := by
  apply neg_eq_of_add_eq_zero
  rw [add_zero]

theorem neg_neg (a : R) : - -a = a := by
  sorry
```

We had to use the annotation `(-0 : R)` instead of `0` in the third theorem
because without specifying `R`
it is impossible for Lean to infer which `0` we have in mind,
and by default it would be interpreted as a natural number.

In Lean, subtraction in a ring is provably equal to
addition of the additive inverse.

```lean
example (a b : R) : a - b = a + -b :=
  sub_eq_add_neg a b
```

On the real numbers, it is _defined_ that way:

```lean
example (a b : ℝ) : a - b = a + -b :=
  rfl

example (a b : ℝ) : a - b = a + -b := by
  rfl
```

The proof term `rfl` is short for "reflexivity".
Presenting it as a proof of `a - b = a + -b` forces Lean
to unfold the definition and recognize both sides as being the same.
The `rfl` tactic does the same.
This is an instance of what is known as a _definitional equality_
in Lean's underlying logic.
This means that not only can one rewrite with `sub_eq_add_neg`
to replace `a - b = a + -b`,
but in some contexts, when dealing with the real numbers,
you can use the two sides of the equation interchangeably.
For example, you now have enough information to prove the theorem
`self_sub` from the last section:

```lean
theorem self_sub (a : R) : a - a = 0 := by
sorry
```

Show that you can prove this using `rw`,
but if you replace the arbitrary ring `R` by
the real numbers, you can also prove it
using either `apply` or `exact`.

Lean knows that `1 + 1 = 2` holds in any ring.
With a bit of effort,
you can use that to prove the theorem `two_mul` from
the last section:

```lean
theorem one_add_one_eq_two : 1 + 1 = (2 : R) := by
  norm_num

theorem two_mul (a : R) : 2 * a = a + a := by
  sorry
```

We close this section by noting that some of the facts about
addition and negation that we established above do not
need the full strength of the ring axioms, or even
commutativity of addition. The weaker notion of a _group_
can be axiomatized as follows:

```lean
variable (A : Type*) [AddGroup A]

#check (add_assoc : ∀ a b c : A, a + b + c = a + (b + c))
#check (zero_add : ∀ a : A, 0 + a = a)
#check (add_left_neg : ∀ a : A, -a + a = 0)
```

It is conventional to use additive notation when
the group operation is commutative,
and multiplicative notation otherwise.
So Lean defines a multiplicative version as well as the
additive version (and also their abelian variants,
`AddCommGroup` and `CommGroup`).

```lean
variable {G : Type*} [Group G]

rcheck (mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))
#check (one_mul : ∀ a : G, 1 * a = a)
#check (mul_left_inv : ∀ a : G, a⁻¹ * a = 1)
```

If you are feeling cocky, try proving the following facts about
groups, using only these axioms.
You will need to prove a number of helper lemmas along the way.
The proofs we have carried out in this section provide some hints.

```lean
theorem mul_right_inv (a : G) : a \* a⁻¹ = 1 := by
  sorry

theorem mul_one (a : G) : a * 1 = a := by
  sorry

theorem mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  sorry
```

Explicitly invoking those lemmas is tedious, so Mathlib provides
tactics similar to `ring` in order to cover most uses: `group`
is for non-commutative multiplicative groups, `abel` for abelian
additive groups, and `noncomm_ring` for non-commutative rings.
It may seem odd that the algebraic structures are called
`Ring` and `CommRing` while the tactics are named
`noncomm_ring` and `ring`. This is partly for historical reasons,
but also for the convenience of using a shorter name for the
tactic that deals with commutative rings, since it is used more often.

## Using Theorems and Lemmas

<!-- TODO:fix numref -->

Rewriting is great for proving equations,
but what about other sorts of theorems?
For example, how can we prove an inequality,
like the fact that :math:`a + e^b \le a + e^c` holds whenever :math:`b \le c`?
We have already seen that theorems can be applied to arguments and hypotheses,
and that the `apply` and `exact` tactics can be used to solve goals.
In this section, we will make good use of these tools.

Consider the library theorems `le_refl` and `le_trans`:

```lean
#check (le_refl : ∀ a : ℝ, a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)
```

As we explain in more detail in :numref:`implication_and_the_universal_quantifier`,
the implicit parentheses in the statement of `le_trans`
associate to the right, so it should be interpreted as `a ≤ b → (b ≤ c → a ≤ c)`.
The library designers have set the arguments `a`, `b` and `c` to `le_trans` implicit,
so that Lean will _not_ let you provide them explicitly (unless you
really insist, as we will discuss later).
Rather, it expects to infer them from the context in which they are used.
For example, when hypotheses `h : a ≤ b` and `h' : b ≤ c`
are in the context,
all the following work:

```lean
variable (h : a ≤ b) (h' : b ≤ c)

#check (le_refl : ∀ a : Real, a ≤ a)
#check (le_refl a : a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)
#check (le_trans h : b ≤ c → a ≤ c)
#check (le_trans h h' : a ≤ c)
```

The `apply` tactic takes a proof of a general statement or implication,
tries to match the conclusion with the current goal,
and leaves the hypotheses, if any, as new goals.
If the given proof matches the goal exactly
(modulo _definitional_ equality),
you can use the `exact` tactic instead of `apply`.
So, all of these work:

```lean
example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  apply le_trans
    apply h₀
    apply h₁

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  apply le_trans h₀
  apply h₁

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z :=
  le_trans h₀ h₁

example (x : ℝ) : x ≤ x := by
  apply le_refl

example (x : ℝ) : x ≤ x :=
  le_refl x
```

In the first example, applying `le_trans`
creates two goals,
and we use the dots to indicate where the proof of each begins.
The dots are optional, but they serve to _focus_ the goal:
within the block introduced by the dot, only one goal is visible,
and it must be completed before the end of the block.
Here we end the first block by starting a new one with another dot.
We could just as well have decreased the indentation.
In the fourth example and in the last example,
we avoid going into tactic mode entirely:
`le_trans h₀ h₁` and `le_refl x` are the proof terms we need.

Here are a few more library theorems:

```lean
#check (le_refl : ∀ a, a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)
#check (lt_of_le_of_lt : a ≤ b → b < c → a < c)
#check (lt_of_lt_of_le : a < b → b ≤ c → a < c)
#check (lt_trans : a < b → b < c → a < c)
```

Use them together with `apply` and `exact` to prove the following:

```lean
example (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  sorry
```

In fact, Lean has a tactic that does this sort of thing automatically:

```lean
example (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  linarith
```

The `linarith` tactic is designed to handle _linear arithmetic_.

```lean
example (h : 2 * a ≤ 3 * b) (h' : 1 ≤ a) (h'' : d = 2) : d + a ≤ 5 * b := by
  linarith
```

In addition to equations and inequalities in the context,
`linarith` will use additional inequalities that you pass as arguments.
In the next example, `exp_le_exp.mpr h'` is a proof of
`exp b ≤ exp c`, as we will explain in a moment.
Notice that, in Lean, we write `f x` to denote the application
of a function `f` to the argument `x`,
exactly the same way we write `h x` to denote the result of
applying a fact or theorem `h` to the argument `x`.
Parentheses are only needed for compound arguments,
as in `f (x + y)`. Without the parentheses, `f x + y`
would be parsed as `(f x) + y`.

```lean
example (h : 1 ≤ a) (h' : b ≤ c) : 2 + a + exp b ≤ 3 * a + exp c := by
  linarith [exp_le_exp.mpr h']
```

Here are some more theorems in the library that can be used to establish
inequalities on the real numbers.

```lean
#check (exp_le_exp : exp a ≤ exp b ↔ a ≤ b)
#check (exp_lt_exp : exp a < exp b ↔ a < b)
#check (log_le_log : 0 < a → a ≤ b → log a ≤ log b)
#check (log_lt_log : 0 < a → a < b → log a < log b)
#check (add_le_add : a ≤ b → c ≤ d → a + c ≤ b + d)
#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (add_le_add_right : a ≤ b → ∀ c, a + c ≤ b + c)
#check (add_lt_add_of_le_of_lt : a ≤ b → c < d → a + c < b + d)
#check (add_lt_add_of_lt_of_le : a < b → c ≤ d → a + c < b + d)
#check (add_lt_add_left : a < b → ∀ c, c + a < c + b)
#check (add_lt_add_right : a < b → ∀ c, a + c < b + c)
#check (add_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a + b)
#check (add_pos : 0 < a → 0 < b → 0 < a + b)
#check (add_pos_of_pos_of_nonneg : 0 < a → 0 ≤ b → 0 < a + b)
#check (exp_pos : ∀ a, 0 < exp a)
#check add_le_add_left
```

Some of the theorems, `exp_le_exp`, `exp_lt_exp`
use a _bi-implication_, which represents the
phrase "if and only if."
(You can type it in VS Code with `\lr` of `\iff`).
We will discuss this connective in greater detail in the next chapter.
Such a theorem can be used with `rw` to rewrite a goal to
an equivalent one:

```lean
example (h : a ≤ b) : exp a ≤ exp b := by
  rw [exp_le_exp]
  exact h
```

In this section, however, we will use the fact that if `h : A ↔ B`
is such an equivalence,
then `h.mp` establishes the forward direction, `A → B`,
and `h.mpr` establishes the reverse direction, `B → A`.
Here, `mp` stands for "modus ponens" and
`mpr` stands for "modus ponens reverse."
You can also use `h.1` and `h.2` for `h.mp` and `h.mpr`,
respectively, if you prefer.
Thus the following proof works:

```lean
example (h₀ : a ≤ b) (h₁ : c < d) : a + exp c + e < b + exp d + e := by
  apply add_lt_add_of_lt_of_le
  · apply add_lt_add_of_le_of_lt h₀
    apply exp_lt_exp.mpr h₁
  apply le_refl
```

The first line, `apply add_lt_add_of_lt_of_le`,
creates two goals,
and once again we use a dot to separate the
proof of the first from the proof of the second.

Try the following examples on your own.
The example in the middle shows you that the `norm_num`
tactic can be used to solve concrete numeric goals.

```lean
example (h₀ : d ≤ e) : c + exp (a + d) ≤ c + exp (a + e) := by sorry

example : (0 : ℝ) < 1 := by norm_num

example (h : a ≤ b) : log (1 + exp a) ≤ log (1 + exp b) := by
  have h₀ : 0 < 1 + exp a := by sorry
  apply log_le_log h₀
  sorry
```

From these examples, it should be clear that being able to
find the library theorems you need constitutes an important
part of formalization.
There are a number of strategies you can use:

- You can browse Mathlib in its
  [GitHub repository](https://github.com/leanprover-community/mathlib4).

- You can use the API documentation on the Mathlib
  [web pages](https://leanprover-community.github.io/mathlib4_docs).

- You can rely on Mathlib naming conventions and Ctrl-space completion in
  the editor to guess a theorem name (or Cmd-space on a Mac keyboard).
  In Lean, a theorem named `A_of_B_of_C` establishes
  something of the form `A` from hypotheses of the form `B` and `C`,
  where `A`, `B`, and `C`
  approximate the way we might read the goals out loud.
  So a theorem establishing something like `x + y ≤ ...` will probably
  start with `add_le`.
  Typing `add_le` and hitting Ctrl-space will give you some helpful choices.
  Note that hitting Ctrl-space twice displays more information about the available
  completions.

- If you right-click on an existing theorem name in VS Code,
  the editor will show a menu with the option to
  jump to the file where the theorem is defined,
  and you can find similar theorems nearby.

- You can use the `apply?` tactic,
  which tries to find the relevant theorem in the library.

```lean
example : 0 ≤ a ^ 2 := by
  -- apply?
  exact sq_nonneg a
```

To try out `apply?` in this example,
delete the `exact` command and uncomment the previous line.
Using these tricks,
see if you can find what you need to do the
next example:

```lean
example (h : a ≤ b) : c - exp b ≤ c - exp a := by
  sorry
```

Using the same tricks, confirm that `linarith` instead of `apply?`
can also finish the job.

Here is another example of an inequality:

```lean
example : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  have h : 0 ≤ a ^ 2 - 2 * a * b + b ^ 2
  calc
    a ^ 2 - 2 * a * b + b ^ 2 = (a - b) ^ 2 := by ring
    _ ≥ 0 := by apply pow_two_nonneg

  calc
    2 * a * b = 2 * a * b + 0 := by ring
    _ ≤ 2 * a * b + (a ^ 2 - 2 * a * b + b ^ 2) := add_le_add (le_refl _) h
    _ = a ^ 2 + b ^ 2 := by ring
```

Mathlib tends to put spaces around binary operations like `*` and `^`,
but in this example, the more compressed format increases readability.
There are a number of things worth noticing.
First, an expression `s ≥ t` is definitionally equivalent to `t ≤ s`.
In principle, this means one should be able to use them interchangeably.
But some of Lean's automation does not recognize the equivalence,
so Mathlib tends to favor `≤` over `≥`.
Second, we have used the `ring` tactic extensively.
It is a real timesaver!
Finally, notice that in the second line of the
second `calc` proof,
instead of writing `by exact add_le_add (le_refl _) h`,
we can simply write the proof term `add_le_add (le_refl _) h`.

In fact, the only cleverness in the proof above is figuring
out the hypothesis `h`.
Once we have it, the second calculation involves only
linear arithmetic, and `linarith` can handle it:

```lean
example : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  have h : 0 ≤ a ^ 2 - 2 * a * b + b ^ 2
  calc
    a ^ 2 - 2 * a * b + b ^ 2 = (a - b) ^ 2 := by ring
    _ ≥ 0 := by apply pow_two_nonneg
  linarith
```

How nice! We challenge you to use these ideas to prove the
following theorem. You can use the theorem `abs_le'.mpr`.
You will also need the `constructor` tactic to split a conjunction
to two goals; see :numref:`conjunction_and_biimplication`.

```lean
example : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
  sorry

#check abs_le'.mpr
```

If you managed to solve this, congratulations!
You are well on your way to becoming a master formalizer.

## More examples using apply and rw

The `min` function on the real numbers is uniquely characterized
by the following three facts:
section

```lean
#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)
```

Can you guess the names of the theorems that characterize
`max` in a similar way?

Notice that we have to apply `min` to a pair of arguments `a` and `b`
by writing `min a b` rather than `min (a, b)`.
Formally, `min` is a function of type `ℝ → ℝ → ℝ`.
When we write a type like this with multiple arrows,
the convention is that the implicit parentheses associate
to the right, so the type is interpreted as `ℝ → (ℝ → ℝ)`.
The net effect is that if `a` and `b` have type `ℝ`
then `min a` has type `ℝ → ℝ` and
`min a b` has type `ℝ`, so `min` acts like a function
of two arguments, as we expect. Handling multiple
arguments in this way is known as _currying_,
after the logician Haskell Curry.

The order of operations in Lean can also take some getting used to.
Function application binds tighter than infix operations, so the
expression `min a b + c` is interpreted as `(min a b) + c`.
With time, these conventions will become second nature.

Using the theorem `le_antisymm`, we can show that two
real numbers are equal if each is less than or equal to the other.
Using this and the facts above,
we can show that `min` is commutative:

```lean
example : min a b = min b a := by
  apply le_antisymm
  · show min a b ≤ min b a
    apply le_min
    · apply min_le_right
    apply min_le_left
  · show min b a ≤ min a b
    apply le_min
    · apply min_le_right
    apply min_le_left
```

Here we have used dots to separate proofs of
different goals.
Our usage is inconsistent:
at the outer level,
we use dots and indentation for both goals,
whereas for the nested proofs,
we use dots only until a single goal remains.
Both conventions are reasonable and useful.
We also use the `show` tactic to structure
the proof
and indicate what is being proved in each block.
The proof still works without the `show` commands,
but using them makes the proof easier to read and maintain.

It may bother you that the proof is repetitive.
To foreshadow skills you will learn later on,
we note that one way to avoid the repetition
is to state a local lemma and then use it:

```lean
example : min a b = min b a := by
  have h : ∀ x y : ℝ, min x y ≤ min y x := by
    intro x y
    apply le_min
    apply min_le_right
    apply min_le_left
  apply le_antisymm
  apply h
  apply h
```

We will say more about the universal quantifier in
:numref:`implication_and_the_universal_quantifier`,
but suffice it to say here that the hypothesis
`h` says that the desired inequality holds for
any `x` and `y`,
and the `intro` tactic introduces an arbitrary
`x` and `y` to establish the conclusion.
The first `apply` after `le_antisymm` implicitly
uses `h a b`, whereas the second one uses `h b a`.

Another solution is to use the `repeat` tactic,
which applies a tactic (or a block) as many times
as it can.

```lean
example : min a b = min b a := by
  apply le_antisymm
  repeat
    apply le_min
    apply min_le_right
    apply min_le_left
```

We encourage you to prove the following as exercises.
You can use either of the tricks just described to shorten the first.

```lean
example : max a b = max b a := by
  sorry
example : min (min a b) c = min a (min b c) := by
  sorry
```

Of course, you are welcome to prove the associativity of `max` as well.

It is an interesting fact that `min` distributes over `max`
the way that multiplication distributes over addition,
and vice-versa.
In other words, on the real numbers, we have the identity
`min a (max b c) = max (min a b) (min a c)`
as well as the corresponding version with `max` and `min`
switched.
But in the next section we will see that this does _not_ follow
from the transitivity and reflexivity of `≤` and
the characterizing properties of `min` and `max` enumerated above.
We need to use the fact that `≤` on the real numbers is a _total order_,
which is to say,
it satisfies `∀ x y, x ≤ y ∨ y ≤ x`.
Here the disjunction symbol, `∨`, represents "or".
In the first case, we have `min x y = x`,
and in the second case, we have `min x y = y`.
We will learn how to reason by cases in :numref:`disjunction`,
but for now we will stick to examples that don't require the case split.

Here is one such example:

```lean
theorem aux : min a b + c ≤ min (a + c) (b + c) := by
  sorry
example : min a b + c = min (a + c) (b + c) := by
  sorry
```

It is clear that `aux` provides one of the two inequalities
needed to prove the equality,
but applying it to suitable values yields the other direction
as well.
As a hint, you can use the theorem `add_neg_cancel_right`
and the `linarith` tactic.

Lean's naming convention is made manifest
in the library's name for the triangle inequality:

```lean
#check (abs_add : ∀ a b : ℝ, |a + b| ≤ |a| + |b|)
```

Use it to prove the following variant, using also `add_sub_cancel_right`:

```lean
example : |a| - |b| ≤ |a - b| :=
  sorry
end
```

See if you can do this in three lines or less.
You can use the theorem `sub_add_cancel`.

Another important relation that we will make use of
in the sections to come is the divisibility relation
on the natural numbers, `x ∣ y`.
Be careful: the divisibility symbol is _not_ the
ordinary bar on your keyboard.
Rather, it is a unicode character obtained by
typing `\|` in VS Code.
By convention, Mathlib uses `dvd`
to refer to it in theorem names.

```lean
example (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
  dvd_trans h₀ h₁

example : x ∣ y * x * z := by
  apply dvd_mul_of_dvd_left
  apply dvd_mul_left

example : x ∣ x ^ 2 := by
  apply dvd_mul_left
```

In the last example, the exponent is a natural
number, and applying `dvd_mul_left`
forces Lean to expand the definition of `x^2` to
`x^1 * x`.
See if you can guess the names of the theorems
you need to prove the following:

```lean
example (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
  sorry
end
```

With respect to divisibility, the _greatest common divisor_,
`gcd`, and least common multiple, `lcm`,
are analogous to `min` and `max`.
Since every number divides `0`,
`0` is really the greatest element with respect to divisibility:

```lean
variable (m n : ℕ)

#check (Nat.gcd_zero_right n : Nat.gcd n 0 = n)
#check (Nat.gcd_zero_left n : Nat.gcd 0 n = n)
#check (Nat.lcm_zero_right n : Nat.lcm n 0 = 0)
#check (Nat.lcm_zero_left n : Nat.lcm 0 n = 0)
```

See if you can guess the names of the theorems you will need to
prove the following:

```lean
example : Nat.gcd m n = Nat.gcd n m := by
  sorry
```

Hint: you can use `dvd_antisymm`, but if you do, Lean will
complain that the expression is ambiguous between the generic
theorem and the version `Nat.dvd_antisymm`,
the one specifically for the natural numbers.
You can use `_root_.dvd_antisymm` to specify the generic one;
either one will work.
