import LeanCourse.Common
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Pow
set_option linter.unusedVariables false
noncomputable section
open BigOperators Function Set Real Filter Classical Topology
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

/-
* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapters 9 and 10, all sections

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  Feel free to skip exercises if you are confident that you can do them.
  There are solutions in the solution folder in case you get stuck.

# You have two options for this assignment

1. Hand in the solutions to the exercises below. Deadline: 24.11.2023.
2. If you have already chosen a project, and your project doesn't require topology or analysis, you can work on your project. If you do, push a decent amount of work to your fork of the repository by 24.11. In this case you do not have to upload anything on eCampus.

* When you hand in your solution, make sure that the file compiles!
  If you didn't manage to complete a particular exercise, make sure that the proof still compiles,
  by replacing the proof (or part of the proof) by `sorry`.
-/


#check Filter.Eventually.filter_mono
#check Filter.Eventually.mono
/- Here is a technical exercise using filters,
that was useful in something I did recently. Useful lemmas here are
* `Filter.Eventually.filter_mono`
* `Filter.Eventually.mono` -/
example (p q r: Prop) (h : p) : (if p then q else r) = q := by exact if_pos h

example (p q r: Prop) (h : ¬p) : (if p then q else r) = r := by exact if_neg h

example (p q: Prop) : ((p ↔ q) → (p → q)) := fun x ↦ x.1

example (p q: Prop) : ((p ↔ q) ↔ (¬p ↔ ¬q)) := by rw [not_iff_not]

#check Iff.symm

example {ι α : Type*} {p q : ι → Prop} {L : Filter ι} ( h: ∀ᶠ i in L, p i ∧ q i ) : ∀ᶠ i in L, p i := by
  apply Filter.Eventually.mono h
  exact fun _ ↦ (fun h ↦ h.1)

example (p q : Prop) (h: p ∧ q) : p ↔ q := ⟨fun _ ↦ h.2, fun _ ↦ h.1⟩

lemma exercise6_1 {ι α : Type*} {p : ι → Prop} {q : Prop} {a b : α}
    {L : Filter ι} {F G : Filter α}
    (hbF : ∀ᶠ x in F, x ≠ b) (haG : ∀ᶠ x in G, x ≠ a) (haF : pure a ≤ F) (hbG : pure b ≤ G) :
    (∀ᶠ i in L, p i ↔ q) ↔
    Tendsto (fun i ↦ if p i then a else b) L (if q then F else G) := by
  have hab : a ≠ b
  · by_contra hab
    rw [hab] at haF
    simp [eventually_iff] at hbF
    specialize haF hbF
    simp at haF hbF
  rw [tendsto_iff_eventually]
  by_cases q
  constructor
  . intro hL f hα
    simp [if_pos h] at hα
    specialize haF hα
    simp at haF
    have : ∀ᶠ i in L, q := by simp [eventually_iff]; simp [h];
    -- eventually_const.mpr h does not work
    have : ∀ᶠ (i : ι) in L, p i := (eventually_congr hL).mpr this
    apply Filter.Eventually.mono this
    intro x hx
    simpa [if_pos hx]
  . intro h1
    simp [if_pos h] at h1
    specialize h1 hbF
    simp [eventually_iff, hab] at h1
    have : ∀ᶠ x in L, p x:= h1
    apply Filter.Eventually.mono this
    exact fun _ ↦ (fun hpx ↦ ⟨fun _ ↦ h, fun _ ↦ hpx⟩)
  constructor
  . intro hL f hα
    simp [if_neg h] at hα
    specialize hbG hα
    simp at hbG
    have : ∀ᶠ i in L, ¬q := by simp [eventually_iff]; simp [h];
    -- rw [not_iff_not] at hL does not work
    simp [eventually_iff, h] at hL
    -- have : ∀ᶠ (i : ι) in L, ¬ p i := (eventually_congr hL).mpr this
    apply Filter.Eventually.mono hL
    intro x hnpx
    simpa [if_neg hnpx]
  . intro h1
    simp [if_neg h] at h1
    specialize h1 haG
    simp [eventually_iff, hab.symm] at h1
    have : ∀ᶠ x in L, ¬ p x:= h1
    apply Filter.Eventually.mono this
    -- exact fun _ ↦ (fun hnpx ↦ ⟨fun hpx ↦ hnpx hpx, fun _ ↦ hpx⟩)
    intro x hx
    rw [← not_iff_not]
    exact ⟨fun _ ↦ h, fun _ ↦ hx⟩


/- To be more concrete, we can use the previous lemma to prove the following.
if we denote the characteristic function of `A` by `1_A`, and `f : ℝ → ℝ` is a function,
then  `f * 1_{s i}` tends to `f * 1_t` iff `x ∈ s i` eventually means the same as `x ∈ t` for all `x`. (note that this does *not* necessarily mean that `s i = t` eventually).
Here it lemmas are `indicator_apply` and `apply_ite` -/
lemma exercise6_2 {ι : Type*} {L : Filter ι} {s : ι → Set ℝ} {t : Set ℝ} {f : ℝ → ℝ}
    (ha : ∀ x, f x ≠ 0) :
    (∀ x, ∀ᶠ i in L, x ∈ s i ↔ x ∈ t) ↔
    Tendsto (fun i ↦ Set.indicator (s i) f) L (𝓝 (Set.indicator t f)) := by
  rw [tendsto_pi_nhds]
  simp [Set.indicator]
  have (x : ℝ) : 𝓝 (if x ∈ t then f x else 0) = if x ∈ t then 𝓝 (f x) else 𝓝 (0) := by
    by_cases h: x ∈ t
    simp [if_pos h]
    simp [if_neg h]
  -- how to rw [...] in a ∀ formula
  have aux (x : ℝ) : f x ∉ Ioo (-|(f x)/2|) (|(f x)/2|) := by
    simp
    by_cases h : f x > 0
    have : f x / 2 > 0 := by linarith
    intro
    rw [abs_eq_self.mpr]
    linarith
    gcongr
    intro h'
    have : f x / 2 ≤ 0 := by linarith
    rw [abs_eq_neg_self.mpr] at h'
    simp at h'
    exfalso
    apply h h'
    exact this
  have aux' (x : ℝ) : 0 ∈ Ioo (-|(f x)/2|) (|(f x)/2|) := by simp; exact ha x
  have hx (x : ℝ) : ∀ᶠ y in 𝓝 0, y ≠ f x := by
    simp [eventually_nhds_iff]
    use Ioo (-|(f x)/2|) (|(f x)/2|)
    constructor
    . intro x'
      contrapose!
      intro h
      rw [h]
      exact aux x
    . exact ⟨isOpen_Ioo, aux' x⟩

  have h0 (x : ℝ) : ∀ᶠ y in 𝓝 (f x), y ≠ 0 := by
    simp [eventually_nhds_iff]
    sorry
  have aux'' (x : ℝ) : pure x ≤ 𝓝 x := by simp
  have hx'  (x : ℝ) : pure (f x) ≤ 𝓝 (f x) := aux'' (f x) -- can be done by simp
  have h0' : pure (0 : ℝ)  ≤ 𝓝 0 := aux'' 0 -- why can't be donw by simp... may be coersion
  constructor
  . intro h x
    rw [this x]
    specialize h x
    exact (exercise6_1 (h0 x) (hx x) (hx' x) h0').mp h
  . intro h x
    specialize h x
    rw [this x] at h
    exact (exercise6_1 (h0 x) (hx x) (hx' x) h0').mpr h

#check abs_eq_self
#check abs_eq_neg_self
#check IsOpen.exists_Ioo_subset

section

variable (α : Type*)
 [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α] [DenselyOrdered α]

/-
In the next three exercises we will show that every continuous injective function `ℝ → ℝ` is
either strictly monotone or strictly antitone.

We start by proving a slightly harder version of the exercise in class.
We generalize the real numbers to an arbitrary type `α`
that satisfies all the conditions required for the intermediate value theorem.
If you want to prove this by using the intermediate value theorem only once,
then use `intermediate_value_uIcc`.
`uIcc a b` is the unordered interval `[min a b, max a b]`.
Useful lemmas: `uIcc_of_le` and `mem_uIcc`. -/
lemma exercise6_3 {f : α → α} (hf : Continuous f) (h2f : Injective f) {a b x : α}
    (hab : a ≤ b) (h2ab : f a < f b) (hx : a ≤ x) : f a ≤ f x := by
      by_contra h
      push_neg at h
      have : uIcc (f x) (f b) ⊆ f '' uIcc x b := intermediate_value_uIcc (Continuous.continuousOn hf)
      have hfa : f a ∈ uIcc (f x) (f b) := by
        rw [mem_uIcc]
        left
        exact ⟨le_of_lt h, le_of_lt h2ab⟩
      specialize this hfa
      obtain ⟨x', hx'1, hx'2⟩ := this
      specialize h2f hx'2
      rw [h2f] at hx'1
      have : x = a := by
        rw [mem_uIcc] at hx'1
        rcases hx'1 with hx'1' | hx'1''
        . apply le_antisymm hx'1'.1 hx
        . rw [le_antisymm hx'1''.1 hab] at h2ab
          simp at h2ab
      rw [this] at h
      simp at h


/- Now use this and the intermediate value theorem again
to prove that `f` is at least monotone on `[a, ∞)`. -/
lemma exercise6_4 {f : α → α} (hf : Continuous f) (h2f : Injective f) {a b : α}
    (hab : a ≤ b) (h2ab : f a < f b) : StrictMonoOn f (Ici a) := by
  simp [StrictMonoOn]
  intro x hx y hy hxy
  have ax : f a ≤ f x := exercise6_3 _ hf h2f hab h2ab hx -- why a placeholder here??
  have ay : f a ≤ f y := exercise6_3 _ hf h2f hab h2ab hy
  by_contra hfxy
  push_neg at hfxy
  have : uIcc (f a) (f x) ⊆ f '' uIcc a x := intermediate_value_uIcc (Continuous.continuousOn hf)
  have ayx : f y ∈ uIcc (f a) (f x) := by
    rw [mem_uIcc]
    left
    exact ⟨ay, hfxy⟩
  specialize this ayx
  obtain ⟨y', hy'1, hy'2⟩ := this
  specialize h2f hy'2
  rw [h2f, uIcc_of_le hx] at hy'1
  have : y < y := gt_of_gt_of_ge hxy hy'1.2
  simp at this


example (a b : ℝ) (h1 : a ≤ b) (h2 : b < a) : a < a := by exact gt_of_gt_of_ge h2 h1

example (a b : ℝ) (h1 : a < b) (h2 : b ≤ a) : a < a := by exact lt_of_lt_of_le h1 h2

/-
Now we can finish just by using the previous exercise multiple times.
In this proof we take advantage that we did the previous exercise for an arbitrary order,
because that allows us to apply it to `ℝ` with the reversed order `≥`.
This is called `OrderDual ℝ`. This allows us to get that `f` is also strictly monotone on
`(-∞, b]`.
Now finish the proof yourself.
You do not need to apply the intermediate value theorem in this exercise.
-/
lemma my_lemma_for_6_5 (f : ℝ → ℝ) (hf : Continuous f) (h2f : Injective f) (hf01 : f 0 < f 1):
    StrictMono f := by
  have h3f : ∀ {a b : ℝ} (hab : a ≤ b) (h2ab : f a < f b), StrictMonoOn f (Iic b)
  · intro a b hab h2ab
    have := exercise6_4 (OrderDual ℝ) hf h2f hab h2ab
    convert this using 0
    exact strict_mono_on_dual_iff.symm
  intro a b hab
  by_cases hb1 : b ≤ 1
  -- simp [StrictMonoOn] at h3f
  . exact h3f (by norm_num) hf01 (le_of_lt (lt_of_lt_of_le hab hb1)) hb1 hab
  . push_neg at hb1
    have hb0 : 0 ≤ b := by linarith
    by_cases ha0 : 0 ≤ a
    . exact exercise6_4 _ hf h2f (by norm_num) hf01 ha0 hb0 hab
    . push_neg at ha0
      have ha1 : a ≤ 1 := by linarith
      have : f b > f 1 := exercise6_4 _ hf h2f (by norm_num) hf01 (by norm_num) hb0 hb1
      have : f a < f 0 := h3f (by norm_num) hf01 ha1 (by norm_num) ha0
      linarith


example (a b : ℝ) (h1 : a ≤ b) (h2 : a ≠ b) : a < b := by exact Ne.lt_of_le h2 h1

example (f : ℝ → ℝ) (hf : Continuous f) : Continuous (-f) := Continuous.neg hf

#check Continuous.neg
#check Injective

lemma exercise6_5 (f : ℝ → ℝ) (hf : Continuous f) (h2f : Injective f) :
    StrictMono f ∨ StrictAnti f := by
    by_cases hf01 : f 0 < f 1

    left
    exact my_lemma_for_6_5 f hf h2f hf01

    right
    push_neg at hf01
    rw [Injective] at h2f
    have h_negf01 : -f 0 < -f 1 := by
      simp; apply Ne.lt_of_le _ hf01;
      by_contra h
      specialize h2f h
      norm_num at h2f
    have h_negf : Continuous (-f) := Continuous.neg hf
    have h_2negf : Injective (-f) := by simp [Injective]; exact h2f
    have smono_negf: StrictMono (-f) := my_lemma_for_6_5 (-f) h_negf h_2negf h_negf01
    intro a b hab
    have : -f a < -f b := smono_negf hab
    linarith



/-
Let's prove that the absolute value function is not differentiable at 0.
You can do this by showing that the left derivative and the right derivative do exist,
but are not equal. We can state this with `HasDerivWithinAt`
To make the proof go through, we need to show that the intervals have unique derivatives.
An example of a set that doesn't have unique derivatives is the set `ℝ × {0}`
as a subset of `ℝ × ℝ`, since that set doesn't contains only points in the `x`-axis,
so within that set there is no way to know what the derivative of a function should be
in the direction of the `y`-axis.

The following lemmas will be useful
* `HasDerivWithinAt.congr`
* `uniqueDiffWithinAt_convex`
* `HasDerivWithinAt.derivWithin`
* `DifferentiableAt.derivWithin`.
-/
#check HasDerivWithinAt.congr
#check HasDerivWithinAt.derivWithin
#check DifferentiableAt.derivWithin
#check hasDerivWithinAt_id
#check hasDerivWithinAt_neg
#check uniqueDiffWithinAt_convex
#check Convex

lemma exercise6_6 : ¬ DifferentiableAt ℝ (fun x : ℝ ↦ |x|) 0 := by
  intro h
  have h1' : HasDerivWithinAt (fun x : ℝ ↦ x) 1 (Ici 0) 0
  . apply hasDerivWithinAt_id -- exact does not work lol
  have h1 : HasDerivWithinAt (fun x : ℝ ↦ |x|) 1 (Ici 0) 0
  · apply HasDerivWithinAt.congr h1'
    <;> simp
  have h2' : HasDerivWithinAt (fun x : ℝ ↦ -x) (-1) (Iic 0) 0
  . apply hasDerivWithinAt_neg
  have h2 : HasDerivWithinAt (fun x : ℝ ↦ |x|) (-1) (Iic 0) 0
  · apply HasDerivWithinAt.congr h2'
    <;> simp
  have h3 : UniqueDiffWithinAt ℝ (Ici (0 : ℝ)) 0 := by
    apply uniqueDiffWithinAt_convex
    exact convex_Ici 0
    simp
    simp -- why doesn't <;> simp work here??
  have h4 : UniqueDiffWithinAt ℝ (Iic (0 : ℝ)) 0 := by
    apply uniqueDiffWithinAt_convex
    exact convex_Iic 0
    simp
    simp
  have c1 : deriv (fun x : ℝ ↦ |x|) 0 = 1 := by
    rw [← DifferentiableAt.derivWithin h h3]
    exact HasDerivWithinAt.derivWithin h1 h3
  have c2 : deriv (fun x : ℝ ↦ |x|) 0 = -1 := by
    rw [← DifferentiableAt.derivWithin h h4]
    exact HasDerivWithinAt.derivWithin h2 h4
  rw [c1] at c2
  norm_num at c2
