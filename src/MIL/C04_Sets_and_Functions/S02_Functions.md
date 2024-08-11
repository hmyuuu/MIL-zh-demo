## Functions

If `f : α → β` is a function and `p` is a set of
elements of type `β`,
the library defines `preimage f p`, written `f ⁻¹' p`,
to be `{x | f x ∈ p}`.
The expression `x ∈ f ⁻¹' p` reduces to `f x ∈ p`.
This is often convenient, as in the following example:

```lean
variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

open Function
open Set

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  ext
  rfl
```

If `s` is a set of elements of type `α`,
the library also defines `image f s`,
written `f '' s`,
to be `{y | ∃ x, x ∈ s ∧ f x = y}`.
So a hypothesis `y ∈ f '' s` decomposes to a triple
`⟨x, xs, xeq⟩` with `x : α` satisfying the hypotheses `xs : x ∈ s`
and `xeq : f x = y`.
The `rfl` tag in the `rintro` tactic (see :numref:`the_existential_quantifier`) was made precisely
for this sort of situation.

```lean
example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y; constructor
  · rintro ⟨x, xs | xt, rfl⟩
    · left
      use x, xs
    right
    use x, xt
  rintro (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩)
  · use x, Or.inl xs
  use x, Or.inr xt
```

Notice also that the `use` tactic applies `rfl`
to close goals when it can.

Here is another example:

```lean
example : s ⊆ f ⁻¹' (f '' s) := by
  intro x xs
  show f x ∈ f '' s
  use x, xs
```

We can replace the line `use x, xs` by
`apply mem_image_of_mem f xs` if we want to
use a theorem specifically designed for that purpose.
But knowing that the image is defined in terms
of an existential quantifier is often convenient.

The following equivalence is a good exercise:

```lean
example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  sorry
```

It shows that `image f` and `preimage f` are
an instance of what is known as a _Galois connection_
between `Set α` and `Set β`,
each partially ordered by the subset relation.
In the library, this equivalence is named
`image_subset_iff`.
In practice, the right-hand side is often the
more useful representation,
because `y ∈ f ⁻¹' t` unfolds to `f y ∈ t`
whereas working with `x ∈ f '' s` requires
decomposing an existential quantifier.

Here is a long list of set-theoretic identities for
you to enjoy.
You don't have to do all of them at once;
do a few of them,
and set the rest aside for a rainy day.

```lean
example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  sorry

example : f '' (f ⁻¹' u) ⊆ u := by
  sorry

example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  sorry

example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  sorry

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  sorry

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  sorry

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  sorry

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  sorry

example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  sorry

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
  sorry

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  sorry

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  sorry

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  sorry

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  sorry
```

You can also try your hand at the next group of exercises,
which characterize the behavior of images and preimages
with respect to indexed unions and intersections.
In the third exercise, the argument `i : I` is needed
to guarantee that the index set is nonempty.
To prove any of these, we recommend using `ext` or `intro`
to unfold the meaning of an equation or inclusion between sets,
and then calling `simp` to unpack the conditions for membership.

```lean
variable {I : Type*} (A : I → Set α) (B : I → Set β)

example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  sorry

example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  sorry

example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
  sorry

example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
  sorry

example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
  sorry
```

The library defines a predicate `InjOn f s` to say that
`f` is injective on `s`.
It is defined as follows:

```lean

example : InjOn f s ↔ ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂ :=
  Iff.refl _
```

-- BOTH:
end

The statement `Injective f` is provably equivalent
to `InjOn f univ`.
Similarly, the library defines `range f` to be
`{x | ∃y, f y = x}`,
so `range f` is provably equal to `f '' univ`.
This is a common theme in Mathlib:
although many properties of functions are defined relative
to their full domain,
there are often relativized versions that restrict
the statements to a subset of the domain type.

Here is are some examples of `InjOn` and `range` in use:
BOTH: -/
section

```lean
open Set Real

-- EXAMPLES:
example : InjOn log { x | x > 0 } := by
  intro x xpos y ypos
  intro e
  -- log x = log y
  calc
    x = exp (log x) := by rw [exp_log xpos]
    _ = exp (log y) := by rw [e]
    _ = y := by rw [exp_log ypos]


example : range exp = { y | y > 0 } := by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    apply exp_pos
  intro ypos
  use log y
  rw [exp_log ypos]
```

Try proving these:
EXAMPLES: -/

```lean
example : InjOn sqrt { x | x ≥ 0 } := by
  sorry

example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  sorry

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  sorry

example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  sorry
```

-- SOLUTIONS:
example : InjOn sqrt { x | x ≥ 0 } := by
intro x xnonneg y ynonneg
intro e
calc
x = sqrt x ^ 2 := by rw [sq_sqrt xnonneg]
_ = sqrt y ^ 2 := by rw [e]
_ = y := by rw [sq_sqrt ynonneg]

example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
intro x xnonneg y ynonneg
intro e
dsimp at \*
calc
x = sqrt (x ^ 2) := by rw [sqrt_sq xnonneg]
_ = sqrt (y ^ 2) := by rw [e]
_ = y := by rw [sqrt_sq ynonneg]

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
ext y; constructor
· rintro ⟨x, ⟨xnonneg, rfl⟩⟩
apply sqrt_nonneg
intro ynonneg
use y ^ 2
dsimp at \*
constructor
apply pow_nonneg ynonneg
apply sqrt_sq
assumption

example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
ext y
constructor
· rintro ⟨x, rfl⟩
dsimp at \*
apply pow_two_nonneg
intro ynonneg
use sqrt y
exact sq_sqrt ynonneg

-- BOTH:
end

To define the inverse of a function `f : α → β`,
we will use two new ingredients.
First, we need to deal with the fact that
an arbitrary type in Lean may be empty.
To define the inverse to `f` at `y` when there is
no `x` satisfying `f x = y`,
we want to assign a default value in `α`.
Adding the annotation `[Inhabited α]` as a variable
is tantamount to assuming that `α` has a
preferred element, which is denoted `default`.
Second, in the case where there is more than one `x`
such that `f x = y`,
the inverse function needs to _choose_ one of them.
This requires an appeal to the _axiom of choice_.
Lean allows various ways of accessing it;
one convenient method is to use the classical `choose`
operator, illustrated below.

-- BOTH:
section

```lean
variable {α β : Type*} [Inhabited α]

-- EXAMPLES:
#check (default : α)

variable (P : α → Prop) (h : ∃ x, P x)

#check Classical.choose h

example : P (Classical.choose h) :=
  Classical.choose_spec h
```

Given `h : ∃ x, P x`, the value of `Classical.choose h`
is some `x` satisfying `P x`.
The theorem `Classical.choose_spec h` says that `Classical.choose h`
meets this specification.

With these in hand, we can define the inverse function
as follows:
BOTH: -/

```lean
noncomputable section

open Classical

def inverse (f : α → β) : β → α := fun y : β ↦
  if h : ∃ x, f x = y then Classical.choose h else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := by
  rw [inverse, dif_pos h]
  exact Classical.choose_spec h
```

The lines `noncomputable section` and `open Classical`
are needed because we are using classical logic in an essential way.
On input `y`, the function `inverse f`
returns some value of `x` satisfying `f x = y` if there is one,
and a default element of `α` otherwise.
This is an instance of a _dependent if_ construction,
since in the positive case, the value returned,
`Classical.choose h`, depends on the assumption `h`.
The identity `dif_pos h` rewrites `if h : e then a else b`
to `a` given `h : e`,
and, similarly, `dif_neg h` rewrites it to `b` given `h : ¬ e`.
There are also versions `if_pos` and `if_neg` that works for non-dependent
if constructions and will be used in the next section.
The theorem `inverse_spec` says that `inverse f`
meets the first part of this specification.

Don't worry if you do not fully understand how these work.
The theorem `inverse_spec` alone should be enough to show
that `inverse f` is a left inverse if and only if `f` is injective
and a right inverse if and only if `f` is surjective.
Look up the definition of `LeftInverse` and `RightInverse`
by double-clicking or right-clicking on them in VS Code,
or using the commands `#print LeftInverse` and `#print RightInverse`.
Then try to prove the two theorems.
They are tricky!
It helps to do the proofs on paper before
you start hacking through the details.
You should be able to prove each of them with about a half-dozen
short lines.
If you are looking for an extra challenge,
try to condense each proof to a single-line proof term.
BOTH: -/

```lean
variable (f : α → β)

open Function

-- EXAMPLES:
example : Injective f ↔ LeftInverse (inverse f) f :=
  sorry

example : Surjective f ↔ RightInverse (inverse f) f :=
  sorry
```

-- SOLUTIONS:
example : Injective f ↔ LeftInverse (inverse f) f := by
constructor
· intro h y
apply h
apply inverse_spec
use y
intro h x1 x2 e
rw [← h x1, ← h x2, e]

example : Injective f ↔ LeftInverse (inverse f) f :=
⟨fun h y ↦ h (inverse*spec * ⟨y, rfl⟩), fun h x1 x2 e ↦ by rw [← h x1, ← h x2, e]⟩

example : Surjective f ↔ RightInverse (inverse f) f := by
constructor
· intro h y
apply inverse_spec
apply h
intro h y
use inverse f y
apply h

example : Surjective f ↔ RightInverse (inverse f) f :=
⟨fun h y ↦ inverse*spec * (h _), fun h y ↦ ⟨inverse f y, h _⟩⟩

-- BOTH:
end

-- OMIT:
/-
.. TODO: These comments after this paragraph are from Patrick.
.. We should decide whether we want to do this here.
.. Another possibility is to wait until later.
.. There may be good examples for the topology chapter,
.. at which point, the reader will be more of an expert.

.. This may be a good place to also introduce a discussion of the choose tactic, and explain why you choose (!) not to use it here.

.. Typically, you can include:

.. example {α β : Type\*} {f : α → β} : surjective f ↔ ∃ g : β → α, ∀ b, f (g b) = b :=
.. begin
.. split,
.. { intro h,
.. dsimp [surjective] at h, -- this line is optional
.. choose g hg using h,
.. use g,
.. exact hg },
.. { rintro ⟨g, hg⟩,
.. intros b,
.. use g b,
.. exact hg b },
.. end
.. Then contrast this to a situation where we really want a def outputting an element or a function, maybe with a less artificial example than your inverse.

.. We should also tie this to the "function are global" discussion, and the whole thread of deferring proofs to lemmas instead of definitions. There is a lot going on here, and all of it is crucial for formalization.
-/

We close this section with a type-theoretic statement of Cantor's
famous theorem that there is no surjective function from a set
to its power set.
See if you can understand the proof,
and then fill in the two lines that are missing.

-- BOTH:
section
variable {α : Type\*}
open Function

-- EXAMPLES:

```lean
theorem Cantor : ∀ f : α → Set α, ¬Surjective f := by
  intro f surjf
  let S := { i | i ∉ f i }
  rcases surjf S with ⟨j, h⟩
  have h₁ : j ∉ f j := by
    intro h'
    have : j ∉ f j := by rwa [h] at h'
    contradiction
  have h₂ : j ∈ S
  sorry
  have h₃ : j ∉ S
  sorry
  contradiction
```

-- COMMENTS: TODO: improve this
-- SOLUTIONS:
theorem Cantorαα : ∀ f : α → Set α, ¬Surjective f := by
intro f surjf
let S := { i | i ∉ f i }
rcases surjf S with ⟨j, h⟩
have h₁ : j ∉ f j := by
intro h'
have : j ∉ f j := by rwa [h] at h'
contradiction
have h₂ : j ∈ S := h₁
have h₃ : j ∉ S := by rwa [h] at h₁
contradiction

-- BOTH:
end
