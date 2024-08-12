## The Schröder-Bernstein Theorem

We close this chapter with an elementary but nontrivial theorem of set theory.
Let $\alpha$ and $\beta$ be sets.
(In our formalization, they will actually be types.)
Suppose $f : \alpha → \beta$ and $g : \beta → \alpha$
are both injective.
Intuitively, this means that $\alpha$ is no bigger than $\beta$ and vice-versa.
If $\alpha$ and $\beta$ are finite, this implies that
they have the same cardinality, which is equivalent to saying that there
is a bijection between them.
In the nineteenth century, Cantor stated that same result holds even in the
case where $\alpha$ and $\beta$ are infinite.
This was eventually established by Dedekind, Schröder, and Bernstein
independently.

Our formalization will introduce some new methods that we will explain
in greater detail in chapters to come.
Don't worry if they go by too quickly here.
Our goal is to show you that you already have the skills to contribute
to the formal proof of a real mathematical result.

To understand the idea behind the proof, consider the image of the map
$g$ in $\alpha$.
On that image, the inverse of $g$ is defined and is a bijection
with $\beta$.

The problem is that the bijection does not include the shaded region
in the diagram, which is nonempty if $g$ is not surjective.
Alternatively, we can use $f$ to map all of
$\alpha$ to $\beta$,
but in that case the problem is that if $f$ is not surjective,
it will miss some elements of $\beta$.

But now consider the composition $g \circ f$ from $\alpha$ to
itself. Because the composition is injective, it forms a bijection between
$\alpha$ and its image, yielding a scaled-down copy of $alpha$
inside itself.

<!-- .. image:: /figures/schroeder_bernstein3. -->

This composition maps the inner shaded ring to yet another such
set, which we can think of as an even smaller concentric shaded ring,
and so on.
This yields a
concentric sequence of shaded rings, each of which is in
bijective correspondence with the next.
If we map each ring to the next and leave the unshaded
parts of $\alpha$ alone,
we have a bijection of $\alpha$ with the image of $g$.
Composing with $g^{-1}$, this yields the desired
bijection between $\alpha$ and $\beta$.

We can describe this bijection more simply.
Let $A$ be the union of the sequence of shaded regions, and
define $h : \alpha \to \beta$ as follows:

$$
h(x) = \begin{cases}
f(x) & \text{if $x \in A$} \\
g^{-1}(x) & \text{otherwise.}
\end{cases}
$$

In other words, we use $f$ on the shaded parts,
and we use the inverse of $g$ everywhere else.
The resulting map $h$ is injective
because each component is injective
and the images of the two components are disjoint.
To see that it is surjective,
suppose we are given a $y$ in $\beta$, and
consider $g(y)$.
If $g(y)$ is in one of the shaded regions,
it cannot be in the first ring, so we have $g(y) = g(f(x))$
for some $x$ is in the previous ring.
By the injectivity of $g$, we have $h(x) = f(x) = y$.
If $g(y)$ is not in the shaded region,
then by the definition of $h$, we have $h(g(y))= y$.
Either way, $y$ is in the image of $h$.

This argument should sound plausible, but the details are delicate.
Formalizing the proof will not only improve our confidence in the
result, but also help us understand it better.
Because the proof uses classical logic, we tell Lean that our definitions
will generally not be computable.

```lean
noncomputable section
open Classical
variable {α β : Type*} [Nonempty β]
```

The annotation `[Nonempty β]` specifies that `β` is nonempty.
We use it because the Mathlib primitive that we will use to
construct $g^{-1}$ requires it.
The case of the theorem where $\beta$ is empty is trivial,
and even though it would not be hard to generalize the formalization to cover
that case as well, we will not bother.
Specifically, we need the hypothesis `[Nonempty β]` for the operation
`invFun` that is defined in Mathlib.
Given `x : α`, `invFun g x` chooses a preimage of `x`
in `β` if there is one,
and returns an arbitrary element of `β` otherwise.
The function `invFun g` is always a left inverse if `g` is injective
and a right inverse if `g` is surjective.

We define the set corresponding to the union of the shaded regions as follows.

```lean
variable (f : α → β) (g : β → α)

def sbAux : ℕ → Set α
  | 0 => univ \ g '' univ
  | n + 1 => g '' (f '' sbAux n)

def sbSet :=
  ⋃ n, sbAux f g n
```

The definition `sbAux` is an example of a _recursive definition_,
which we will explain in the next chapter.
It defines a sequence of sets

$$
S*0 &= \alpha ∖ g(\beta) \\
S*{n+1} &= g(f(S_n)).
$$

The definition `sbSet` corresponds to the set
$A = \bigcup_{n \in \mathbb{N}} S_n$ in our proof sketch.
The function $h$ described above is now defined as follows:

```lean
def sbFun (x : α) : β :=
  if x ∈ sbSet f g then f x else invFun g x
```

We will need the fact that our definition of $g^{-1}$ is a
right inverse on the complement of $A$,
which is to say, on the non-shaded regions of $\alpha$.
This is so because the outermost ring, $S_0$, is equal to
$\alpha \setminus g(\beta)$, so the complement of $A$ is
contained in $g(\beta)$.
As a result, for every $x$ in the complement of $A$,
there is a $y$ such that $g(y) = x$.
(By the injectivity of $g$, this $y$ is unique,
but next theorem says only that `invFun g x` returns some `y`
such that `g y = x`.)

Step through the proof below, make sure you understand what is going on,
and fill in the remaining parts.
You will need to use `invFun_eq` at the end.
Notice that rewriting with `sbAux` here replaces `sbAux f g 0`
with the right-hand side of the corresponding defining equation.

```lean
theorem sb*right_inv {x : α} (hx : x ∉ sbSet f g) : g (invFun g x) = x := by
  have : x ∈ g '' univ := by
    contrapose! hx
    rw [sbSet, mem_iUnion]
    use 0
    rw [sbAux, mem_diff]
    sorry
  exact ⟨mem_univ *, hx⟩
  have : ∃ y, g y = x := by
    sorry
  sorry
```

We now turn to the proof that $h$ is injective.
Informally, the proof goes as follows.
First, suppose $h(x_1) = h(x_2)$.
If $x_1$ is in $A$, then $h(x_1) = f(x_1)$,
and we can show that $x_2$ is in $A$ as follows.
If it isn't, then we have $h(x_2) = g^{-1}(x_2)$.
From $f(x_1) = h(x_1) = h(x_2)$ we have $g(f(x_1)) = x_2$.
From the definition of $A$, since $x_1$ is in $A$,
$x_2$ is in $A$ as well, a contradiction.
Hence, if $x_1` is in $A$, so is $x_2$,
in which case we have $f(x_1) = h(x_1) = h(x_2) = f(x_2)$.
The injectivity of $f$ then implies $x_1 = x_2$.
The symmetric argument shows that if $x_2$ is in $A$,
then so is $x_1$, which again implies $x_1 = x_2$.

The only remaining possibility is that neither $x_1$ nor $x_2$
is in $A$. In that case, we have
$g^{-1}(x_1) = h(x_1) = h(x_2) = g^{-1}(x_2)$.
Applying $g$ to both sides yields $x_1 = x_2$.

Once again, we encourage you to step through the following proof
to see how the argument plays out in Lean.
See if you can finish off the proof using `sb_right_inv`.

```lean
theorem sb*injective (hf : Injective f) : Injective (sbFun f g) := by
  set A := sbSet f g with A_def
  set h := sbFun f g with h_def
  intro x₁ x₂
  intro (hxeq : h x₁ = h x₂)
  show x₁ = x₂
  simp only [h_def, sbFun, ← A_def] at hxeq
  by_cases xA : x₁ ∈ A ∨ x₂ ∈ A
  · wlog x₁A : x₁ ∈ A generalizing x₁ x₂ hxeq xA
    · symm
      apply this hxeq.symm xA.symm (xA.resolve_left x₁A)
    have x₂A : x₂ ∈ A := by
      apply \_root*.not_imp_self.mp
      intro (x₂nA : x₂ ∉ A)
      rw [if_pos x₁A, if_neg x₂nA] at hxeq
      rw [A_def, sbSet, mem_iUnion] at x₁A
      have x₂eq : x₂ = g (f x₁) := by
        sorry
      rcases x₁A with ⟨n, hn⟩
      rw [A_def, sbSet, mem_iUnion]
      use n + 1
      simp [sbAux]
      exact ⟨x₁, hn, x₂eq.symm⟩
    sorry
  push_neg at xA
  sorry
```

The proof introduces some new tactics.
To start with, notice the `set` tactic, which introduces abbreviations
`A` and `h` for `sbSet f g` and `sb_fun f g` respectively.
We name the corresponding defining equations `A_def` and `h_def`.
The abbreviations are definitional, which is to say, Lean will sometimes
unfold them automatically when needed.
But not always; for example, when using `rw`, we generally need to
use `A_def` and `h_def` explicitly.
So the definitions bring a tradeoff: they can make expressions shorter
and more readable, but they sometimes require us to do more work.

A more interesting tactic is the `wlog` tactic, which encapsulates
the symmetry argument in the informal proof above.
We will not dwell on it now, but notice that it does exactly what we want.
If you hover over the tactic you can take a look at its documentation.

The argument for surjectivity is even easier.
Given $y$ in $\beta$,
we consider two cases, depending on whether $g(y)$ is in $A$.
If it is, it can't be in $S_0$, the outermost ring,
because by definition that is disjoint from the image of $g$.
Thus it is an element of $S_{n+1}$ for some $n$.
This means that it is of the form $g(f(x))$ for some
$x$ in $S_n$.
By the injectivity of $g$, we have $f(x) = y$.
In the case where $g(y)$ is in the complement of $A$,
we immediately have $h(g(y))= y$, and we are done.

Once again, we encourage you to step through the proof and fill in
the missing parts.
The tactic `rcases n with _ | n` splits on the cases `g y ∈ sbAux f g 0`
and `g y ∈ sbAux f g (n + 1)`.
In both cases, calling the simplifier with `simp [sbAux]`
applies the corresponding defining equation of `sbAux`.

```lean
theorem sb_surjective (hg : Injective g) : Surjective (sbFun f g) := by
  set A := sbSet f g with A_def
  set h := sbFun f g with h_def
  intro y
  by_cases gyA : g y ∈ A
  · rw [A_def, sbSet, mem_iUnion] at gyA
    rcases gyA with ⟨n, hn⟩
    rcases n with * | n
    · simp [sbAux] at hn
    simp [sbAux] at hn
    rcases hn with ⟨x, xmem, hx⟩
    use x
    have : x ∈ A := by
      rw [A_def, sbSet, mem_iUnion]
      exact ⟨n, xmem⟩
    simp only [h_def, sbFun, if_pos this]
    exact hg hx
  sorry
```

We can now put it all together. The final statement is short and sweet,
and the proof uses the fact that `Bijective h` unfolds to
`Injective h ∧ Surjective h`.

```lean
theorem schroeder_bernstein {f : α → β} {g : β → α} (hf : Injective f) (hg : Injective g) :
  ∃ h : α → β, Bijective h :=
  ⟨sbFun f g, sb_injective f g hf, sb_surjective f g hg⟩
```
