## Irrational Roots

Let's start with a fact known to the ancient Greeks, namely,
that the square root of 2 is irrational.
If we suppose otherwise,
we can write $\sqrt{2} = a / b$ as a fraction
in lowest terms. Squaring both sides yields $a^2 = 2 b^2$,
which implies that $a$ is even.
If we write $a = 2c$, then we get $4c^2 = 2 b^2$
and hence $b^2 = 2 c^2$.
This implies that $b$ is also even, contradicting
the fact that we have assumed that $a / b$ has been
reduced to lowest terms.

Saying that $a / b$ is a fraction in lowest terms means
that $a$ and $b$ do not have any factors in common,
which is to say, they are _coprime_.
Mathlib defines the predicate `Nat.Coprime m n` to be `Nat.gcd m n = 1`.
Using Lean's anonymous projection notation, if `s` and `t` are
expressions of type `Nat`, we can write `s.Coprime t` instead of
`Nat.Coprime s t`, and similarly for `Nat.gcd`.
As usual, Lean will often unfold the definition of `Nat.Coprime` automatically
when necessary,
but we can also do it manually by rewriting or simplifying with
the identifier `Nat.Coprime`.
The `norm_num` tactic is smart enough to compute concrete values.

```lean
#print Nat.Coprime

example (m n : Nat) (h : m.Coprime n) : m.gcd n = 1 :=
  h

example (m n : Nat) (h : m.Coprime n) : m.gcd n = 1 := by
  rw [Nat.Coprime] at h
  exact h

example : Nat.Coprime 12 7 := by norm_num

example : Nat.gcd 12 8 = 4 := by norm_num
```

We have already encountered the `gcd` function in
:numref:`more_on_order_and_divisibility`.
There is also a version of `gcd` for the integers;
we will return to a discussion of the relationship between
different number systems below.
There are even a generic `gcd` function and generic
notions of `Prime` and `Coprime`
that make sense in general classes of algebraic structures.
We will come to understand how Lean manages this generality
in the next chapter.
In the meanwhile, in this section, we will restrict attention
to the natural numbers.

We also need the notion of a prime number, `Nat.Prime`.
The theorem `Nat.prime_def_lt` provides one familiar characterization,
and `Nat.Prime.eq_one_or_self_of_dvd` provides another.

```lean
#check Nat.prime_def_lt

example (p : ℕ) (prime_p : Nat.Prime p) : 2 ≤ p ∧ ∀ m : ℕ, m < p → m ∣ p → m = 1 := by
  rwa [Nat.prime_def_lt] at prime_p

#check Nat.Prime.eq_one_or_self_of_dvd

example (p : ℕ) (prime_p : Nat.Prime p) : ∀ m : ℕ, m ∣ p → m = 1 ∨ m = p :=
  prime_p.eq_one_or_self_of_dvd

example : Nat.Prime 17 := by norm_num

-- commonly used
example : Nat.Prime 2 :=
  Nat.prime_two

example : Nat.Prime 3 :=
  Nat.prime_three
```

In the natural numbers, a prime number has the property that it cannot
be written as a product of nontrivial factors.
In a broader mathematical context, an element of a ring that has this property
is said to be _irreducible_.
An element of a ring is said to be _prime_ if whenever it divides a product,
it divides one of the factors.
It is an important property of the natural numbers
that in that setting the two notions coincide,
giving rise to the theorem `Nat.Prime.dvd_mul`.

We can use this fact to establish a key property in the argument
above:
if the square of a number is even, then that number is even as well.
Mathlib defines the predicate `Even` in `Algebra.Group.Even`,
but for reasons that will become clear below,
we will simply use `2 ∣ m` to express that `m` is even.

```lean
#check Nat.Prime.dvd_mul
#check Nat.Prime.dvd_mul Nat.prime_two
#check Nat.prime_two.dvd_mul

theorem even_of_even_sqr {m : ℕ} (h : 2 ∣ m ^ 2) : 2 ∣ m := by
  rw [pow_two, Nat.prime_two.dvd_mul] at h
  cases h <;> assumption

example {m : ℕ} (h : 2 ∣ m ^ 2) : 2 ∣ m :=
  Nat.Prime.dvd_of_dvd_pow Nat.prime_two h
```

As we proceed, you will need to become proficient at finding the facts you
need.
Remember that if you can guess the prefix of the name and
you have imported the relevant library,
you can use tab completion (sometimes with `ctrl-tab`) to find
what you are looking for.
You can use `ctrl-click` on any identifier to jump to the file
where it is defined, which enables you to browse definitions and theorems
nearby.
You can also use the search engine on the
[Lean community web pages](https://leanprover-community.github.io/),
and if all else fails,
don't hesitate to ask on
[Zulip](https://leanprover.zulipchat.com/).

```lean
example (a b c : Nat) (h : a * b = a * c) (h' : a ≠ 0) : b = c :=
  -- apply? suggests the following:
  (mul_right_inj' h').mp h
```

The heart of our proof of the irrationality of the square root of two
is contained in the following theorem.
See if you can fill out the proof sketch, using
`even_of_even_sqr` and the theorem `Nat.dvd_gcd`.

```lean
example {m n : ℕ} (coprime_mn : m.Coprime n) : m ^ 2 ≠ 2 * n ^ 2 := by
  intro sqr_eq
  have : 2 ∣ m := by
    sorry
  obtain ⟨k, meq⟩ := dvd_iff_exists_eq_mul_left.mp this
  have : 2 * (2 * k ^ 2) = 2 * n ^ 2 := by
    rw [← sqr_eq, meq]
    ring
  have : 2 * k ^ 2 = n ^ 2 :=
    sorry
  have : 2 ∣ n := by
    sorry
  have : 2 ∣ m.gcd n := by
    sorry
  have : 2 ∣ 1 := by
    sorry
    convert this
  norm_num at this
```

In fact, with very few changes, we can replace `2` by an arbitrary prime.
Give it a try in the next example.
At the end of the proof, you'll need to derive a contradiction from
`p ∣ 1`.
You can use `Nat.Prime.two_le`, which says that
any prime number is greater than or equal to two,
and `Nat.le_of_dvd`.

```lean
example {m n p : ℕ} (coprime_mn : m.Coprime n) (prime_p : p.Prime) : m ^ 2 ≠ p * n ^ 2 := by
  sorry
```

Let us consider another approach.
Here is a quick proof that if $p$ is prime, then
$m^2 \ne p n^2$: if we assume $m^2 = p n^2$
and consider the factorization of $m` and :math:`n$ into primes,
then $p$ occurs an even number of times on the left side of the equation
and an odd number of times on the right, a contradiction.
Note that this argument requires that $n$ and hence $m$
are not equal to zero.
The formalization below confirms that this assumption is sufficient.

The unique factorization theorem says that any natural number other
than zero can be written as the product of primes in a unique way.
Mathlib contains a formal version of this, expressed in terms of a function
`Nat.factors`, which returns the list of
prime factors of a number in nondecreasing order.
The library proves that all the elements of `Nat.factors n`
are prime, that any `n` greater than zero is equal to the
product of its factors,
and that if `n` is equal to the product of another list of prime numbers,
then that list is a permutation of `Nat.factors n`.

```lean
#check Nat.factors
#check Nat.prime_of_mem_factors
#check Nat.prod_factors
#check Nat.factors_unique
```

You can browse these theorems and others nearby, even though we have not
talked about list membership, products, or permutations yet.
We won't need any of that for the task at hand.
We will instead use the fact that Mathlib has a function `Nat.factorization`,
that represents the same data as a function.
Specifically, `Nat.factorization n p`, which we can also write
`n.factorization p`, returns the multiplicity of `p` in the prime
factorization of `n`. We will use the following three facts.

```lean
theorem factorization_mul' {m n : ℕ} (mnez : m ≠ 0) (nnez : n ≠ 0) (p : ℕ) :
    (m * n).factorization p = m.factorization p + n.factorization p := by
  rw [Nat.factorization_mul mnez nnez]
  rfl

theorem factorization_pow' (n k p : ℕ) :
    (n ^ k).factorization p = k * n.factorization p := by
  rw [Nat.factorization_pow]
  rfl

theorem Nat.Prime.factorization' {p : ℕ} (prime_p : p.Prime) :
    p.factorization p = 1 := by
  rw [prime_p.factorization]
  simp
```

In fact, `n.factorization` is defined in Lean as a function of finite support,
which explains the strange notation you will see as you step through the
proofs above. Don't worry about this now. For our purposes here, we can use
the three theorems above as a black box.

The next example shows that the simplifier is smart enough to replace
`n^2 ≠ 0` by `n ≠ 0`. The tactic `simpa` just calls `simp`
followed by `assumption`.

See if you can use the identities above to fill in the missing parts
of the proof.

```lean
example {m n p : ℕ} (nnz : n ≠ 0) (prime_p : p.Prime) : m ^ 2 ≠ p * n ^ 2 := by
  intro sqr_eq
  have nsqr_nez : n ^ 2 ≠ 0 := by simpa
  have eq1 : Nat.factorization (m ^ 2) p = 2 * m.factorization p := by
    sorry
  have eq2 : (p * n ^ 2).factorization p = 2 * n.factorization p + 1 := by
    sorry
  have : 2 * m.factorization p % 2 = (2 * n.factorization p + 1) % 2 := by
    rw [← eq1, sqr_eq, eq2]
  rw [add_comm, Nat.add_mul_mod_self_left, Nat.mul_mod_right] at this
  norm_num at this
```

A nice thing about this proof is that it also generalizes. There is
nothing special about `2`; with small changes, the proof shows that
whenever we write `m^k = r * n^k`, the multiplicity of any prime `p`
in `r` has to be a multiple of `k`.

To use `Nat.count_factors_mul_of_pos` with `r * n^k`,
we need to know that `r` is positive.
But when `r` is zero, the theorem below is trivial, and easily
proved by the simplifier.
So the proof is carried out in cases.
The line `rcases r with _ | r` replaces the goal with two versions:
one in which `r` is replaced by `0`,
and the other in which `r` is replaces by `r + 1`.
In the second case, we can use the theorem `r.succ_ne_zero`, which
establishes `r + 1 ≠ 0` (`succ` stands for successor).

Notice also that the line that begins `have : npow_nz` provides a
short proof-term proof of `n^k ≠ 0`.
To understand how it works, try replacing it with a tactic proof,
and then think about how the tactics describe the proof term.

See if you can fill in the missing parts of the proof below.
At the very end, you can use `Nat.dvd_sub'` and `Nat.dvd_mul_right`
to finish it off.

Note that this example does not assume that `p` is prime, but the
conclusion is trivial when `p` is not prime since `r.factorization p`
is then zero by definition, and the proof works in all cases anyway.

```lean
example {m n k r : ℕ} (nnz : n ≠ 0) (pow_eq : m ^ k = r * n ^ k) {p : ℕ} :
    k ∣ r.factorization p := by
  rcases r with _ | r
  · simp
  have npow_nz : n ^ k ≠ 0 := fun npowz ↦ nnz (pow_eq_zero npowz)
  have eq1 : (m ^ k).factorization p = k * m.factorization p := by
    sorry
  have eq2 : ((r + 1) * n ^ k).factorization p =
      k * n.factorization p + (r + 1).factorization p := by
    sorry
  have : r.succ.factorization p = k * m.factorization p - k * n.factorization p := by
    rw [← eq1, pow_eq, eq2, add_comm, Nat.add_sub_cancel]
  rw [this]
  sorry
```

There are a number of ways in which we might want to improve on these results.
To start with, a proof that the square root of two is irrational
should say something about the square root of two,
which can be understood as an element of the
real or complex numbers.
And stating that it is irrational should say something about the
rational numbers, namely, that no rational number is equal to it.
Moreover, we should extend the theorems in this section to the integers.
Although it is mathematically obvious that if we could write the square root of
two as a quotient of two integers then we could write it as a quotient
of two natural numbers,
proving this formally requires some effort.

In Mathlib, the natural numbers, the integers, the rationals, the reals,
and the complex numbers are represented by separate data types.
Restricting attention to the separate domains is often helpful:
we will see that it is easy to do induction on the natural numbers,
and it is easiest to reason about divisibility of integers when the
real numbers are not part of the picture.
But having to mediate between the different domains is a headache,
one we will have to contend with.
We will return to this issue later in this chapter.

We should also expect to be able to strengthen the conclusion of the
last theorem to say that the number `r` is a `k`-th power,
since its `k`-th root is just the product of each prime dividing `r`
raised to its multiplicity in `r` divided by `k`.
To be able to do that we will need better means for reasoning about
products and sums over a finite set,
which is also a topic we will return to.

In fact, the results in this section are all established in much
greater generality in Mathlib,
in `Data.Real.Irrational`.
The notion of `multiplicity` is defined for an
arbitrary commutative monoid,
and that it takes values in the extended natural numbers `enat`,
which adds the value infinity to the natural numbers.
In the next chapter, we will begin to develop the means to
appreciate the way that Lean supports this sort of generality.
