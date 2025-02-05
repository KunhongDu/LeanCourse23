import LeanCourse.Common
import Mathlib.Analysis.Complex.Polynomial
import Mathlib.FieldTheory.Minpoly.Basic
open BigOperators Function Ideal Polynomial Classical Matrix
noncomputable section
set_option linter.unusedVariables false
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)


/- # Today: Abstract algebra

We cover section 8.2 from Mathematics in Lean and a bit of field theory and linear algebra.
Chapter 7 covers some of the design decisions for algebraic structures.
I recommend that you read through it, but I won't cover it in detail in class. -/

/-
Last time we discussed projects and group theory
-/


/- # Rings -/

/- Lean uses `Ring` and `CommRing` for rings and commutative rings. -/
example : CommRing ℤ := by infer_instance

/- Also important are *semirings*, which are rings without postulating negation. -/
example : CommSemiring ℕ := by infer_instance


example : Field ℚ := by infer_instance


/- Note that the tactics for computation in a `Ring` vs `CommRing` is
`noncomm_ring` resp. `ring.-/
example {R : Type*} [CommRing R] (x y : R) : (x + y)^2 = x^2 + y^2 + 2*x*y := by ring

example {R : Type*} [Semiring R] (x y : R) : (x + y)^2 = x^2 + y^2 + x*y + y*x := by noncomm_ring

/- The binomial theorem. Note that the natural number `Nat.choose n m` is coerced to an element of `R` here. -/
-- example {R : Type*} [CommRing R] (x y : R) (n : ℕ) :
--  (x + y) ^ n = ∑ m in Finset.range (n + 1), x ^ m * y ^ (n - m) * Nat.choose n m := by rw?


/- We can write `Rˣ` for the units of a ring (i.e. the elements with a multiplicative inverse). -/
example (x : ℤˣ) : x = 1 ∨ x = -1 := Int.units_eq_one_or x

example {R : Type*} [Ring R] (x : Rˣ) : Group Rˣ := by infer_instance

/- We also have a predicate `IsUnit` stating whether an element of the ring is a unit. -/
-- example {R : Type*} [CommRing R] (x : R) : IsUnit x ↔ ∃ y, x * y = 1 := by exact?

/- We write ring homomorphisms with `→+*`. -/
-- example {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (x y : R) :
    f (x + y) = f x + f y ∧ f (x * y) = f x * f y := ⟨f.map_add x y, f.map_mul x y⟩

/- A subring is a subset of `R` that is an additive subgroup and multiplicative submonoid.

As subgroups, subrings are bundled as a set with closure properties.
They are less useful, since we cannot quotient by a subring.  -/
example {R : Type*} [Ring R] (S : Subring R) : Ring S := by infer_instance



/- ## Ideals -/


section Ring
variable {R : Type*} [CommRing R] {I J : Ideal R}

/- Ideals are additive subgroups that are closed under arbitary multiplication. -/
example {x y : R} (hy : y ∈ I) : x * y ∈ I := I.mul_mem_left x hy

/- There are various operations on ideals. -/

example : I + J = I ⊔ J := rfl

example {x : R} : x ∈ I + J ↔ ∃ a ∈ I, ∃ b ∈ J, a + b = x := by
  simp [Submodule.mem_sup]

example : I * J ≤ I ⊓ J := mul_le_inf

example {x : R} : x ∈ I * J ↔ ∃ a ∈ I, ∃ b ∈ J, a * b = x := by sorry

example : CompleteLattice (Ideal R) := by infer_instance
example : Semiring (Ideal R) := by infer_instance




/- We write `Ideal.span s` for the smallest ideal containing `s`.
In particular, `Ideal.span {a}` is the principal ideal generated by `a`. -/

/- Exercise -/
example (n m : ℤ) : span {n} ⊔ span {m} = span {gcd n m} := by sorry

/- Exercise -/
example (n m : ℤ) : span {n} ⊓ span {m} = span {lcm n m} := by sorry

example (n m : ℤ) : span {n} * span {m} = span {n * m} := by sorry

/- We can quotient a ring by an ideal. -/

example {R : Type*} [CommRing R] (I : Ideal R) : R →+* R ⧸ I :=
  Ideal.Quotient.mk I

example {R : Type*} [CommRing R] (I : Ideal R) [h : I.IsPrime] : IsDomain (R ⧸ I) := by
  show_term infer_instance

example {R : Type*} [CommRing R] (I : Ideal R) [h : I.IsMaximal] : Field (R ⧸ I) :=
  Quotient.field I


/- We can prove the Chinese remainder theorem for ideals. -/

example {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] (f : ι → Ideal R)
    (hf : ∀ i j, i ≠ j → IsCoprime (f i) (f j)) : (R ⧸ ⨅ i, f i) ≃+* Π i, R ⧸ f i :=
  Ideal.quotientInfRingEquivPiQuotient f hf

/- Note that we re-use the generic definition of `IsCoprime` here. -/
#print IsCoprime

/- From this we can easily get the traditional version for `ℤ/nℤ`. -/

example (n : ℕ) : Ring (ZMod n) := by infer_instance

example {ι : Type*} [Fintype ι] (a : ι → ℕ) (ha : ∀ i j, i ≠ j → (a i).Coprime (a j)) :
    ZMod (∏ i, a i) ≃+* ∀ i, ZMod (a i) :=
  ZMod.prodEquivPi a ha



example {R : Type*} [CommRing R] [IsPrincipalIdealRing R] (I : Ideal R) :
    ∃ x : R, I = span {x} := by sorry





#where
variable {A : Type*} [Semiring A] [Algebra R A]


/- # Algebras and polynomials -/

/- An *algebra* (or assiciative unital algebra) `A` over a ring `R`
is a semiring `A` equipped with a ring homomorphism `R →+* A`
whose image commutes with every element of `A`. -/
example : R →+* A := algebraMap R A

example (r : R) (a : A) : algebraMap R A r * a = a * algebraMap R A r := Algebra.commutes r a

/- We can also denote `algebraMap R A r * a` using scalar multiplication as `r • a`. -/
example (r : R) (a : A) : r • a = algebraMap R A r * a := Algebra.smul_def r a

/- Note that if `F` and `E` are both fields,
then `[Algebra F E]` states exactly that `E` is a field extension of `F`. -/


/- An important algebra is the polynomial ring `R[X]` or `Polynomial R`. -/

example {R : Type*} [CommRing R] : R[X] := X

example {R : Type*} [CommRing R] (r : R) : R[X] := X - C r

/- `C` is registered as a ring homomorphism. -/


example {R : Type*} [CommRing R] (r : R) : (X + C r) * (X - C r) = X^2 - C (r ^ 2) := by sorry

/- You can access coefficients using `Polynomial.coeff` -/

example {R : Type*} [CommRing R] (r : R) : (C r).coeff 0 = r := by simp

example {R : Type*} [CommRing R] : (X^2 + 2*X + C 3 : R[X]).coeff 1 = 2 := by simp

/- Defining the degree of a polynomial is tricky because of the special case of the zero polynomial. Mathlib has two variants -/
#check natDegree (R := R)
#check degree (R := R)

/- `WithBot ℕ` can be seen as `ℕ ∪ {-∞}`, except that `-∞` is denoted `⊥`. -/

/- We can evaluate polynomials using `Polynomial.eval`. -/
#check eval (R := R)
example {R : Type*} [CommRing R] (P : R[X]) (x : R) : R := P.eval x

example {R : Type*} [CommRing R] (r : R) : (X - C r).eval r = 0 := by simp

/- If `P : R[X]`, then we often want to evaluate `P` in algebras over `R`. E.g. we want to say that `X ^ 2 - 2 : ℚ[X]` has a root in `ℝ` -/
#check aeval (R := R) (A := A)

example : aeval Complex.I (X ^ 2 + 1 : ℝ[X]) = 0 := by simp



end Ring


/- # Fields

Lean's library contains various results field theory and Galois theory. -/

section Field

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/- Here are some important notions in field theory. -/

#check IntermediateField
#check IsSplittingField
#check IsAlgClosed
#check IsGalois
#check NumberField

example {x : L} (hx : IsAlgebraic K x) : aeval x (minpoly K x) = 0 := by rw [minpoly.aeval]

example : IsAlgClosed ℂ := by infer_instance

end Field






section LinearAlgebra

/- # Modules and vector spaces

Most results in linear algebra are not formulated in terms of vector spaces,
but instead they are generalized to modules over a (semi)ring.

A module `M` over a ring `R` is an abelian group `(M, +)` together with a scalar multiplication
`R → M → M` with appropriate associativity and distributivity laws. -/

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

example (r : R) (x y : M) : r • (x + y) = r • x + r • y := by exact?
example (r s : R) (x : M) : (r + s) • x = r • x + s • x := by exact?
example (r s : R) (x : M) : (r * s) • x = r • s • x := by exact?
example (x : M) : (0 : R) • x = 0 := by exact?
example (x : M) : (1 : R) • x = x := by exact?
example (r : R) : r • (0 : M) = 0 := by exact?

/- We have linear maps between modules. -/
variable {N N' : Type*} [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N']

#check M →ₗ[R] N

example (f : M →ₗ[R] N) (g : M →ₗ[R] N') : M →ₗ[R] N × N' := sorry

example : M × N →ₗ[R] M := sorry

example : M →ₗ[R] M × N := sorry

/- Linear maps themselves form a module over `R` (requires that `R` is commutative) -/
example : Module R (M →ₗ[R] N) := by infer_instance




/- Matrices are defined in Mathlib,
but generally we prefer to work abstractly with vector spaces (or modules) without choosing a basis. So we prefer working with linear maps directly, instead of working with matrices. -/
#check Matrix


example {m n : Type*} (M : Matrix m n R) : Mᵀᵀ = M := rfl

/- Bilinear maps are represented as an iterated linear maps. -/
example (f : M →ₗ[R] N →ₗ[R] N') : N →ₗ[R] M →ₗ[R] N' := f.flip

/- We use `ι → ℝ` to denote `ℝ^n` if `ι` has `n` elements. -/
example {ι : Type*} : Module ℝ (ι → ℝ) := by infer_instance

section product

variable {ι : Type*} {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

/- We can also take a (infinitary) product of modules. -/
example : Module R (Π i, M i) := by infer_instance

example (f : Π i, M i) (i : ι) : M i := f i

example (f : Π i, M i) (i₀ : ι) (x : M i₀) : Π i, M i := fun j : ι ↦ Function.update f i₀ x j

example (r : R) (f : Π i, M i) (i : ι) : (r • f) i = r • f i := sorry

example (r : R) (f : Π i, M i) (i₀ : ι) (x : M i₀) :
    r • Function.update f i₀ x = Function.update (r • f) i₀ (r • x) := by sorry

end product

example {ι : Type*} (b : Basis ι R M) : M ≃ₗ[R] ι →₀ R := b.repr

example {ι : Type*} {v : ι → M} (hli : LinearIndependent R v)
    (hsp : ⊤ ≤ Submodule.span R (Set.range v)) : Basis ι R M := by exact Basis.mk hli hsp

end LinearAlgebra

variable {R M : Type*}


/- # Exercises -/

theorem units_ne_neg_self [Ring R] [CharZero R] (u : Rˣ) : u ≠ -u := by
  by_contra hu
  have : (1 : R)  = -1 := by
    calc (1 : R) = u * u⁻¹ := by exact (Units.mul_inv u).symm
      _ = -u * u⁻¹ := by
        norm_cast
        nth_rw 1 [hu]
      _ = -(u * u⁻¹) := by rw [@neg_mul]
      _ = -1 := by rw [(Units.mul_inv u).symm]
  have : (2 : R) = 0 := by
    calc (2 : R) = 1 + 1 := by exact one_add_one_eq_two.symm
      _ = 1 + -1 := by nth_rw 2 [this]
      _ = 0 := by exact add_neg_self 1
  apply two_ne_zero at this
  exact this

#check two_ne_zero
#check Nat.prime_two

example (n m : ℤ) : span {n} ⊔ span {m} = span {gcd n m} := by
  ext x
  rw [Submodule.mem_sup]
  constructor
  . intro h
    obtain ⟨y, hy, z, hz, hzxy⟩ := h
    rw [mem_span_singleton] at hy
    rw [mem_span_singleton] at hz
    rw [mem_span_singleton, ← hzxy]
    apply dvd_add
    exact dvd_trans (gcd_dvd_left n m) hy
    exact dvd_trans (gcd_dvd_right n m) hz
  . intro h
    rw [mem_span_singleton, gcd_dvd_iff_exists] at h
    obtain ⟨r, s, h⟩ := h
    rw [h]
    use n * r
    --- why is it solved directly??
    simp [mem_span_singleton]

#check mem_span_singleton
#check gcd_dvd_iff_exists

example (n m : ℤ) : span {n} ⊓ span {m} = span {lcm n m} := by
  ext x
  rw [Submodule.mem_inf]
  rw [mem_span_singleton, mem_span_singleton, mem_span_singleton]
  exact lcm_dvd_iff.symm

#check lcm_dvd_iff


/- Show that transposing a matrix gives rise to a linear equivalence. -/
example {m n : Type*} [Ring R] [AddCommGroup M] [Module R M] :
  Matrix m n M ≃ₗ[R] Matrix n m M where
    toFun := fun M ↦ Mᵀ
    map_add' := by simp
    map_smul' := by simp
    invFun := fun M ↦ Mᵀ
    left_inv := by simp [LeftInverse]
    right_inv := by simp [Function.RightInverse, LeftInverse]


/- In a module over a ring with characteristic 2, for every element `m` we have `m + m = 0`. -/
example {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] [CharP R 2] (m : M) :
    m + m = 0 := by
    rw [← two_smul R m]
    have : (2: R) = 0 := CharTwo.two_eq_zero
    rw [this]
    exact zero_smul R m

#check two_smul
#check zero_smul
#check CharTwo.two_eq_zero
#check CharP.cast_eq_zero_iff

section Frobenius

variable (p : ℕ) [hp : Fact p.Prime] (K : Type*) [Field K] [CharP K p] {x : K}
/- Let's define the Frobenius morphism. You can use lemmas from the library -/
def frobeniusMorphism : K →+* K :=
  { toFun := fun x ↦ x^p
    map_one' := by simp
    map_mul' := by simp [mul_pow]
    map_zero' := by simp; exact Fin.size_pos'
    map_add' := fun x y => add_pow_char K x y }

@[simp] lemma frobeniusMorphism_def (x : K) : frobeniusMorphism p K x = x ^ p := rfl

lemma iterate_frobeniusMorphism (n : ℕ) : (frobeniusMorphism p K)^[n] x = x ^ p ^ n := by
  induction n
  case zero => simp
  case succ n hn =>
    simp
    rw [RingHom.iterate_map_pow (frobeniusMorphism p K) x n p, hn]
    ring

example : (frobeniusMorphism p K)^[3] (x ^ 2) = ((frobeniusMorphism p K)^[3] x) ^ 2 := by exact RingHom.iterate_map_pow (frobeniusMorphism p K) x 3 2


#check RingHom.injective_iff_ker_eq_bot

example [Ring R][Ring S](f : R →+* S) (x : R) : x ∈ RingHom.ker f ↔ f x = 0 := by exact RingHom.mem_ker f

lemma frobeniusMorphism_injective : Function.Injective (frobeniusMorphism p K) := by
  have : ∀ x : K, x ^ p = 0 → x = 0 := fun x a => pow_eq_zero a
  rw [RingHom.injective_iff_ker_eq_bot (frobeniusMorphism p K)]
  ext x
  simp [RingHom.mem_ker (frobeniusMorphism p K)]
  constructor
  . exact this x
  . intro hx
    rw [hx]
    simp
    exact Fin.size_pos' --- ehh? confusing lol


example [Finite α] (f : α → α) (h1 : Injective f) : Surjective f := by exact Finite.surjective_of_injective h1


lemma frobeniusMorphism_bijective [Finite K] :
    Function.Bijective (frobeniusMorphism p K) :=
      ⟨frobeniusMorphism_injective p K, Finite.surjective_of_injective (frobeniusMorphism_injective p K)⟩

example [Finite K] [CharP K 2] (x : K) : IsSquare x := by
  -- exact isSquare_of_charTwo' x
  rw [IsSquare]
  rcases (frobeniusMorphism_bijective 2 K).2 x with ⟨r, hx⟩
  use r
  rw [← hx]
  exact sq r

example (f : α → α) (h : Injective f) (n : ℕ) : Injective f^[n] := by exact Injective.iterate h n

example (k : ℕ) (x : K) : x ^ p ^ k = 1 ↔ x = 1 := by
  constructor
  . rw [← iterate_frobeniusMorphism]
    intro h
    have : (frobeniusMorphism p K)^[k] x = (frobeniusMorphism p K)^[k] 1 := by
      rw [h, iterate_frobeniusMorphism, ]
      simp
    exact Injective.iterate (frobeniusMorphism_injective p K) k this

  . intro h; simp [h]

open Nat Finset in
/- Let's prove that the Frobenius morphism is in fact additive, without using that
fact from the library. This exercise is challenging! -/
example (x y : K) : (x + y) ^ p = x ^ p + y ^ p := by
  rw [add_pow]


end Frobenius



/- Let's prove that if `M →ₗ[R] M` forms a module over `R`, then `R` must be a commutative ring.
  We have to additionally assume that `M` contains at least two elements, and
  `smul_eq_zero : r • x = 0 ↔ r = 0 ∨ x = 0` (this is given by the `NoZeroSMulDivisors` class).-/
example {R M M' : Type*} [Ring R] [AddCommGroup M] [Module R M] [Nontrivial M]
    [NoZeroSMulDivisors R M] [Module R (M →ₗ[R] M)]
    (h : ∀ (r : R) (f : M →ₗ[R] M) (x : M), (r • f) x = r • f x)
    (r s : R) : r * s = s * r := by
  sorry
