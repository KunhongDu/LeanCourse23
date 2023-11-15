import LeanCourse.Common
set_option linter.unusedVariables false
open Real Function
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

/-
* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapter 5, all sections (mostly section 2)
  Read chapter 6, all sections (mostly sections 1 and 2).

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  Feel free to skip exercises if you are confident that you can do them.

* You can use any lemmas or tactics from mathlib.

* Hand in the solutions to the exercises below. Deadline: 10.11.2023.

* When you hand in your solution, make sure that the file compiles!
  If you didn't manage to complete a particular exercise, make sure that the proof still compiles,
  by replacing the proof (or part of the proof) by `sorry`.
-/


open Nat Finset BigOperators in
lemma exercise4_1 (n : ℕ) :
    (∑ i in range (n + 1), i ^ 3 : ℚ) = (∑ i in range (n + 1), i : ℚ) ^ 2 := by
    have (k : ℕ): (2:  ℚ) * ∑ x in range (k + 1), (x : ℚ) = (k + 1) ^ 2 - (k + 1) := by
      induction k
      case zero => simp
      case succ k hk =>
        rw [sum_range_succ, mul_add, hk]
        push_cast
        ring
    induction n
    case zero => simp
    case succ n hn =>
      rw [sum_range_succ, sum_range_succ (fun i ↦ (i : ℚ)), add_sq, hn, this n]
      push_cast
      ring

open Set in
/-
Suppose `(A i)_i` is a sequence of sets indexed by a well-ordered type
(this is an order where every nonempty set has a minimum element).
We now define a new sequence by `C n = A n \ (⋃ i < n, A i)`.
In this exercise, we show that the new sequence is pairwise disjoint but has the same union as the
original sequence.
-/
lemma exercise4_2 {ι α : Type*} [LinearOrder ι] [wf : WellFoundedLT ι] (A C : ι → Set α)
  (hC : ∀ i, C i = A i \ ⋃ j < i, A j) : Pairwise (Disjoint on C) ∧ ⋃ i, C i = ⋃ i, A i := by
  have h := wf.wf.has_min
  constructor
  . intro i₁ i₂ hi S hSi₁ hSi₂
    have : C i₁ ∩ C i₂ = (⊥ : Set α) := by
      ext x
      constructor
      . intro hyp
        simp [hC] at hyp
        by_cases hi' : i₁ > i₂
        .  exact (hyp.1.2 i₂ hi') hyp.2.1
        . push_neg at hi'
          exact (hyp.2.2 i₁ (lt_iff_le_and_ne.mpr ⟨hi', hi⟩) ) hyp.1.1
      . exfalso
    rw [← this]
    exact subset_inter hSi₁ hSi₂
  . ext x
    constructor
    . intro hx
      simp at hx
      simp
      rcases hx with ⟨i, hi⟩
      use i
      rw [hC] at hi
      exact hi.1
    . intro hx
      simp at hx
      simp
      rcases hx with ⟨i, hi⟩
      have : Set.Nonempty {j | x ∈ A j} := by use i; exact hi
      specialize h {j | x ∈ A j} this
      rcases h with ⟨j, hj, h⟩
      simp at hj
      use j
      have : x ∉ ⋃ k < j, A k := by
        --- should have a easy lemma to prove this
        contrapose! h
        simp
        simp at h
        rcases h with ⟨i, h⟩
        use i
        exact h.symm
      rw [hC]
      exact ⟨hj, this⟩


/-- Let's prove that the positive reals form a group under multiplication.
Note: in this exercise `rw` and `simp` will not be that helpful, since the definition is hidden
behind notation. But you can use apply to use the lemmas about real numbers.

Note: any field mentioning `div`, `npow` or `zpow` are fields that you don't have to give when
defining a group. These are operations defined in terms of the group structure. -/

def PosReal : Type := {x : ℝ // 0 < x}

@[ext] lemma PosReal.ext (x y : PosReal) (h : x.1 = y.1) : x = y := Subtype.ext h

-- instance : Mul PosReal :=
--  ⟨fun a b ↦ ⟨a.1 * b.1, Real.mul_pos a.2 b.2⟩⟩

lemma exercise4_3 : Group PosReal where
  mul a b := ⟨a.1 * b.1, Real.mul_pos a.2 b.2⟩
  mul_assoc a b c:= by
    ext
    -- have : a * b (failed to synthesize instance HMul)
    -- This is confusing.
    exact mul_assoc a.1 b.1 c.1
  one := ⟨1, by norm_num⟩
  one_mul a := by ext; exact one_mul a.1
  mul_one a := by ext; exact mul_one a.1
  inv a := ⟨ a.1⁻¹, (by norm_num; exact a.2)⟩ -- couldn't find lemma for one_div_pos
  mul_left_inv a := by
    ext
    exact inv_mul_cancel (lt_iff_le_and_ne.mp a.2).2.symm

/- Next, we'll prove that if `2 ^ n - 1` is prime, then `n` is prime.
The first exercise is a preparation, and I've given you a skeleton of the proof for the
second exercise. Note how we do some computations in the integers, since the subtraction on `ℕ`
is less well-behaved.
(The converse is not true, because `89 ∣ 2 ^ 11 - 1`) -/

open Nat in

lemma n_ne_0_1_of_le_2 {n : ℕ} (h₁ : n ≠ 0) (h₂ : n ≠ 1) : 2 ≤ n := by
  have : 0 ≤ n  := by linarith
  have : 0 < n :=  lt_iff_le_and_ne.mpr ⟨this, h₁.symm⟩
  have : 1 < n := lt_iff_le_and_ne.mpr ⟨this, h₂.symm⟩
  exact this



lemma exercise4_4 (n : ℕ) :
    ¬ Nat.Prime n ↔ n = 0 ∨ n = 1 ∨ ∃ a b : ℕ, 2 ≤ a ∧ 2 ≤ b ∧ n = a * b := by
    constructor
    . contrapose!
      intro h
      have n2 : 2 ≤ n := n_ne_0_1_of_le_2 h.1 h.2.1
      rw [Nat.prime_def_lt]
      by_contra h'
      push_neg at h'
      rcases h' n2 with ⟨m, hm, h'1, h'2⟩
      rw [Nat.dvd_iff_div_mul_eq] at h'1
      have hm2 : 2 ≤ m := by
        have h1 : m ≠ 0 := by
          by_contra m0
          simp [m0] at h'1
          exact h.1 h'1.symm
        exact n_ne_0_1_of_le_2 h1 h'2
      have hmn2 : 2 ≤ n / m := by
        have h1 : n / m ≠ 0 := by
          by_contra nm0
          simp [nm0] at h'1
          exact h.1 h'1.symm
        have h2 : n / m ≠ 1 := by
          by_contra nm1
          simp [nm1] at h'1
          exact (lt_iff_le_and_ne.mp hm).2 h'1
        exact n_ne_0_1_of_le_2 h1 h2
      exact h.2.2 (n / m) m hmn2 hm2 h'1.symm
    . contrapose!
      intro h
      rw [Nat.prime_def_lt] at h
      constructor
      . by_contra n0
        rw [n0] at h
        norm_num at h
      . constructor
        . by_contra n1
          rw [n1] at h
          norm_num at h
        . intro a b ha hb
          by_contra hnab
          have hna : a ∣ n := dvd_iff_exists_eq_mul_right.mpr ⟨b, hnab⟩
          have hna' : a < n := by
            by_contra hna'
            push_neg at hna'
            rw [hnab] at hna'
            have : b ≤ 1 := by
              contrapose! hna'
              nth_rw 1 [← mul_one a]
              apply Nat.mul_lt_mul_of_pos_left hna' (by linarith)
            have : 2 ≤ 1 := le_trans hb this
            norm_num at this
          have : a = 1 := h.2 a hna' hna
          rw [this] at ha
          norm_num at ha

#check Nat.le_trans

lemma exercise4_5 (n : ℕ) (hn : Nat.Prime (2 ^ n - 1)) : Nat.Prime n := by
  by_contra h2n
  rw [exercise4_4] at h2n
  obtain rfl|rfl|⟨a, b, ha, hb, rfl⟩ := h2n
  · norm_num at hn
  · norm_num at hn
  have h : (2 : ℤ) ^ a - 1 ∣ (2 : ℤ) ^ (a * b) - 1
  · rw [← Int.modEq_zero_iff_dvd]
    calc (2 : ℤ) ^ (a * b) - 1
        ≡ ((2 : ℤ) ^ a) ^ b - 1 [ZMOD (2 : ℤ) ^ a - 1] := by rw [pow_mul 2 a b]
      _ ≡ (1 : ℤ) ^ b - 1 [ZMOD (2 : ℤ) ^ a - 1] := by sorry
      _ ≡ 0 [ZMOD (2 : ℤ) ^ a - 1] := by rw [one_pow]; ring; rfl
  have : 2 ≤ 2 := by norm_num
  have h2 : 2 ^ 2 ≤ 2 ^ a := by exact (Nat.pow_le_iff_le_right this).mpr ha
  have h3 : 1 ≤ 2 ^ a := by sorry
  have h4 : 2 ^ a - 1 ≠ 1 := by zify; simp [h3]; linarith
  have h5 : 2 ^ a - 1 < 2 ^ (a * b) - 1 := by
    apply tsub_lt_tsub_right_of_le h3
    sorry
  have h6' : 2 ^ 0 ≤ 2 ^ (a * b) := by sorry
  have h6 : 1 ≤ 2 ^ (a * b) := h6'
  have h' : 2 ^ a - 1 ∣ 2 ^ (a * b) - 1
  · norm_cast at h
  rw [Nat.prime_def_lt] at hn
  sorry


#check Nat.pow_le_iff_le_right
#check HMod
/- Here is another exercise about numbers. Make sure you find a simple proof on paper first.
-/
lemma exercise4_6 (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    ¬ IsSquare (a ^ 2 + b) ∨ ¬ IsSquare (b ^ 2 + a) := by sorry
