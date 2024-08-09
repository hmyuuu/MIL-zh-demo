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
but if we wanted to apply `add_left*cancel` to more complicated expressions,
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
theorem mul_zero (a : R) : a \* 0 = 0 := by
have h : a * 0 + a \_ 0 = a \* 0 + 0 := by
rw [← mul_add, add_zero, add_zero]
rw [add_left*cancel h]
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

rcheck (mul*assoc : ∀ a b c : G, a * b * c = a * (b * c))
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

theorem mul\*one\_ (a : G) : a \* 1 = a := by
sorry

theorem mul_inv\*rev (a b : G) : (a \* b)⁻¹ = b⁻¹ \* a⁻¹ := by
sorry
```

-- SOLUTIONS:
theorem mul*right_invαα (a : G) : a \* a⁻¹ = 1 := by
have h : (a * a⁻¹)⁻¹ _ (a \_ a⁻¹ * (a \* a⁻¹)) = 1 := by
rw [mul_assoc, ← mul_assoc a⁻¹ a, mul_left*inv, one_*mul, mul_left*inv]
rw [← h, ← mul_assoc, mul_left*inv, one_*mul]

theorem mul*one*αα (a : G) : a \* 1 = a := by
rw [← mul_left*inv a, ← mul_assoc, mul_right_inv, one_*mul]

theorem mul*inv*revαα (a b : G) : (a _ b)⁻¹ = b⁻¹ \* a⁻¹ := by
rw [← one\_\_mul (b⁻¹ _ a⁻¹), ← mul*left*inv (a _ b), mul_assoc, mul_assoc, ← mul_assoc b b⁻¹,
mul_right_inv, one_\*mul, mul*right_inv, mul\*one*]

-- BOTH:
end MyGroup

end

/- TEXT:
.. index:: group (tactic), tactics ; group, tactics ; noncomm\*ring, tactics ; abel

Explicitly invoking those lemmas is tedious, so Mathlib provides
tactics similar to `ring` in order to cover most uses: `group`
is for non-commutative multiplicative groups, `abel` for abelian
additive groups, and `noncomm*ring` for non-commutative rings.
It may seem odd that the algebraic structures are called
`Ring` and `CommRing` while the tactics are named
`noncomm*ring` and `ring`. This is partly for historical reasons,
but also for the convenience of using a shorter name for the
tactic that deals with commutative rings, since it is used more often.
TEXT. -/
