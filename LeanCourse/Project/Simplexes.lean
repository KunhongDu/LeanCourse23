import LeanCourse.Project.Basics
import Mathlib.AlgebraicTopology.TopologicalSimplex

#check SimplexCategory.toTopMap
open SimplexCategory
open Simplicial BigOperators

variable (x : SimplexCategory)
#check toTopObj x

#check (toTopObj ([0]))
#check (CategoryTheory.forget SimplexCategory).obj ([0])

abbrev Δ (n : ℕ) := toTopObj [n]

@[simp]
lemma test : (CategoryTheory.forget SimplexCategory).obj ([0]) = Fin 1 := rfl

instance : Unique (toTopObj ([0])) where
  default := ⟨fun _ ↦ 1, by ext; simp⟩
  uniq := by
    intro a
    ext i
    simp
    simp at i
    have : i = 0 := by simp
    have : ∑ j : Fin 1, a j = a i := by simp [this]
    rw [← this]
    exact a.2

open TopPair Homology

variable {R : Type*} [Ring R] (H : OrdHomology R)

#check Nontrivial


example : ¬Nontrivial ((H.homology 1).obj (toPair (Δ 0))) := by
  by_contra h
  have : (1 : ℤ) = 0 := by apply H.dimension 1 (Δ 0) h
  norm_num at this
