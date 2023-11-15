import LeanCourse.Common
import Mathlib.Analysis.Complex.Polynomial
import Mathlib.FieldTheory.Minpoly.Basic
open BigOperators Function Ideal Polynomial Classical Matrix
noncomputable section
set_option linter.unusedVariables false
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

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

variable (p : ℕ) [hp : Fact p.Prime] (K : Type*) [Field K] [CharP K p]
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

open Nat Finset -- in
/- Let's prove that the Frobenius morphism is in fact additive, without using that
fact from the library. This exercise is challenging! -/
lemma prime_dvd_comb {p k : ℕ} (hp : Nat.Prime p) (hk : 0 < k ∧ k < p): p ∣ (Nat.choose p k) := by
  sorry

-- #check Nat.factorial
-- n! not working
-- how to introduce a symbol for simplification

-- theorem factorial_succaa (n : ℕ) : n.succ ! = (n + 1) * n ! :=
--  rfl

 example (x y : K) : (x + y) ^ p = x ^ p + y ^ p := by
  rw [add_pow]
  have (m : ℕ) : 0 < m ∧ m < p → (Nat.choose p m : K) = 0 := by
    intro h
    exact (CharP.cast_eq_zero_iff K p (Nat.choose p m)).mpr (prime_dvd_comb hp.out h)
  rw [sum_range_succ]
  sorry

end Frobenius



/- Let's prove that if `M →ₗ[R] M` forms a module over `R`, then `R` must be a commutative ring.
  We have to additionally assume that `M` contains at least two elements, and
  `smul_eq_zero : r • x = 0 ↔ r = 0 ∨ x = 0` (this is given by the `NoZeroSMulDivisors` class).-/
example {R M M' : Type*} [Ring R] [AddCommGroup M] [Module R M] [Nontrivial M]
    [NoZeroSMulDivisors R M] [Module R (M →ₗ[R] M)]
    (h : ∀ (r : R) (f : M →ₗ[R] M) (x : M), (r • f) x = r • f x)
    (r s : R) : r * s = s * r := by
    have : ∀(f : M →ₗ[R] M), ∀ (x: M), (r * s) • f x = (s * r) • f x := by
      intro f x
      have : s • f x = f (s • x) := by exact (LinearMap.map_smul f s x).symm
      calc (r * s) • f x = r • (s • f x) := MulAction.mul_smul r s (f x)
        _ = r • (f (s • x)) := by rw [← LinearMap.map_smul f s x]
        _ = (r • f) (s • x) := by rw [← h r f (s • x)]
        _ = s • ((r • f) x) := LinearMap.map_smul (r • f) s x
        _ = s • (r • f x) := by rw [h r f x]
        _ = (s * r) • f x := smul_smul s r (f x)
    have ext_nonzero : ∃ (x : M), x ≠ 0 := exists_ne 0
    rcases ext_nonzero with ⟨x, x_nt⟩
    specialize this LinearMap.id x
    simp at this
    have : (r * s - s * r) • x = 0 := by simp [sub_smul, this]
    rw [smul_eq_zero] at this
    rcases this with h1 | h2
    . rwa [sub_eq_zero] at h1
    . exfalso
      exact x_nt h2

#check LinearMap.id -- how would it know which module we are talking about??
