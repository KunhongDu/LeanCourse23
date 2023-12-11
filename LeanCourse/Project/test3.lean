import Mathlib.Topology.Category.TopCat.Basic

section one
variable (α β: Type) [TopologicalSpace α] [TopologicalSpace β] (f : α → α) (b : β) (h : (α → α) = (β → β)) (p : (γ : Type) → (γ → γ) → Prop)
-- (hα : α = α') (hβ : β = β')

#check Eq.mp h f
#check Eq.mpr h
#check @Continuous -- β β _ _ (Eq.mp h f)

example (hf : Continuous f) : @Continuous β β _ _ (Eq.mp h f) := by
  sorry

example (hf : Continuous f) : Continuous (Eq.mp h f) := by
  sorry

example (hf : p α f) : ((p α) ∘ (Eq.mpr h)) (Eq.mp h f) := by simp [hf]

example (hf : p α f) : (p β) (Eq.mp h f) := by sorry

example : p β = (p α) ∘ (Eq.mpr h) := by sorry

end one

section two

variable (α β: Type) [TopologicalSpace α] [TopologicalSpace β] (f : α → α) (b : β) (h : α = β ) (p : (γ : Type) → γ → Prop) (x : α)

#check Eq.mp h x

example : p β = (p α) ∘ (Eq.mpr h) := by
  ext x
  constructor
  . intro hx
    have : (p α ∘ Eq.mpr h) x = p α (Eq.mpr h x) := rfl
    rw [this]
    set x' := Eq.mpr h x
    have xx' : x = Eq.mp h x' := by simp
    have aux : (p β ∘ Eq.mp h) x' = p β (Eq.mp h x') := rfl
    rw [← xx'] at aux
    have e : (α → Prop) = (β → Prop) := by simp [h]
    have : p α = Eq.mpr e (p β) := by sorry
  sorry

example (P : (γ : Type) → γ) : P α = Eq.mpr h (P β) := by sorry

/-
α β : Type
inst✝¹ : TopologicalSpace α
inst✝ : TopologicalSpace β
f : α → α
b : β
h : α = β
p : (γ : Type) → γ → Prop
x : α
P : Type → Prop
⊢ P α = sorryAx Prop true

example (P : (γ : Type) → Prop) : P α = h.symm ▸ (P β) := by
-/
example (P : (γ : Type) → γ) : P α = h.symm ▸ (P β) := by sorry

example (Q : Type → Type) (P : (γ : Type) → Q γ) : P α = h.symm ▸ (P β) := by sorry

example (P : (γ : Type) → γ): β := h ▸ (P α)

example (P : (γ : Type) → Prop) : P α = P β := by simp [h]

example : Continuous (Eq.mp h) := by sorry

#check h.symm ▸ h
variable (P : Type → Prop) (q : (γ : Type) → γ)

#check h.symm ▸ (P β)
#check h.symm ▸ (q β)
#check Eq.rec
#check cast

end two

section three
variable (α β α' β' : Type) [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace α'] [TopologicalSpace β'] (hα  : α = α') (hβ : β = β') (f: α → β) (hf : Continuous f)

-- def f' : α' → β' := by rw [← hα, ← hβ]; exact f

-- not even well-defined
-- example : Continuous f' := by
end three

variable (α β: Type) [TopologicalSpace α] [TopologicalSpace β] (f: α → β) (hf : Continuous f)

def α' := α

def β' := β
