/-
  Want to formalize the Eilenberg–Steenrod axioms and show some easy consequences.

  Would use
  1. category
  2. functors
  3. category of pairs of top spaces
  4. category of R-mod
  5. homotopy
  6. exact sequence
-/

-- solving universe problem by simply adding assumption that everthing is in the 0-th universe



import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.Homotopy.Equiv
import Mathlib.CategoryTheory.ConcreteCategory.BundledHom
import Mathlib.Algebra.Category.ModuleCat.Abelian
import LeanCourse.Project.Exact
import Mathlib.AlgebraicTopology.SimplicialSet
noncomputable section
open CategoryTheory Classical

/--
  `TopPair` is a structure consisting a pair of topological spaces with an embedding between them.
-/
@[ext]
structure TopPair where
  total : Type
  sub : Type
  isTotalTopologicalSpace : TopologicalSpace total
  isSubTopologicalSpace : TopologicalSpace sub
  map : sub  → total
  isEmbedding : Embedding map

attribute [instance] TopPair.isTotalTopologicalSpace TopPair.isSubTopologicalSpace


namespace TopPair

/-- ` toPair ` sends a topological space ` α ` to a topological pair ` (α, ∅) `
-/
def toPair (α : Type) [TopologicalSpace α]: TopPair where
  total := α
  sub := Empty
  isTotalTopologicalSpace := by infer_instance
  isSubTopologicalSpace := by infer_instance
  map := Empty.rec
  isEmbedding := by simp [embedding_iff, inducing_iff, Function.Injective]


scoped[TopPair] notation "P("α")" => toPair α


@[simp]
lemma to_pair_total_eq_self {α : Type} [TopologicalSpace α]: (toPair α).total = α := rfl

@[simp]
lemma to_pair_sub_eq_empty {α : Type} [TopologicalSpace α] : (toPair α).sub = Empty := rfl

@[simp]
lemma to_pair_map_empty_rec {α : Type} [TopologicalSpace α]: (toPair α).map = Empty.rec := rfl

/--
  ` toPair₂ ` sends a topological space ` α ` to a topological pair ` (α, α) ` with identity as the
-/
def toPair₂ (α : Type) [TopologicalSpace α]: TopPair where
  total := α
  sub := α
  isTotalTopologicalSpace := by infer_instance
  isSubTopologicalSpace := by infer_instance
  map := id
  isEmbedding := embedding_id

scoped[TopPair] notation "P₂("α")" => toPair₂ α

@[simp]
lemma to_pair'_total_eq_self {α : Type} [TopologicalSpace α]: (toPair₂ α).total = α := rfl

@[simp]
lemma to_pair'_sub_eq_self {α : Type} [TopologicalSpace α] : (toPair₂ α).sub = α := rfl

@[simp]
lemma to_pair'_map_eq_id {α : Type} [TopologicalSpace α]: (toPair₂ α).map = id := rfl

/--
  `SubsetToPair` constructs the TopPair of a topological space and one of its subspace with embedding the inclusion.
-/
def SubsetToPair (α : Type) [TopologicalSpace α] (β : Set α) : TopPair where
  total := α
  sub := β
  isTotalTopologicalSpace := by infer_instance
  isSubTopologicalSpace := by infer_instance
  map := Subtype.val -- fun x ↦ x.1
  isEmbedding := embedding_subtype_val

scoped[TopPair] notation "P("α", "β")" => SubsetToPair α β

@[simp]
lemma subset_to_pair_total_eq_total {α : Type} [TopologicalSpace α] {β : Set α}: P(α, β).total = α := rfl

@[simp]
lemma subset_to_pair_sub_eq_sub {α : Type} [TopologicalSpace α] {β : Set α}: P(α, β).sub = β := rfl

@[simp]
lemma subset_to_pair_map_eq_inc {α : Type} [TopologicalSpace α] {β : Set α}: P(α, β).map = Subtype.val := rfl

/--
  `SubsetToPair₂` works similar as `SubsetToPair` but constructs the TopPair of two of the subspaces of a topological space embedding the inclusion.
-/
def SubsetToPair₂ {α : Type} [TopologicalSpace α] {β γ: Set α} (h : γ ⊆ β): TopPair where
  total := β
  sub := γ
  isTotalTopologicalSpace := by infer_instance
  isSubTopologicalSpace := by infer_instance
  map := fun x ↦ ⟨x.1, h x.2⟩
  isEmbedding := by apply Embedding.codRestrict embedding_subtype_val

scoped[TopPair] notation "Pᵢ("h")" => SubsetToPair₂ h

@[simp]
lemma subset_to_pair_total_eq_total' {α : Type} [TopologicalSpace α] {β γ: Set α} (h : γ ⊆ β): Pᵢ(h).total = β := rfl

@[simp]
lemma subset_to_pair_sub_eq_sub' {α : Type} [TopologicalSpace α] {β γ: Set α} (h : γ ⊆ β): Pᵢ(h).sub = γ := rfl

@[simp]
lemma subset_to_pair_map_eq_inc' {α : Type} [TopologicalSpace α] {β γ: Set α} (h : γ ⊆ β): Pᵢ(h).map = fun x ↦ ⟨x.1, h x.2⟩ := rfl
end TopPair

/--
  A `PairMap` is a continuous map between the total spaces of twos pair with a map between the subspaces such that they commute with the embedding.
-/
@[ext]
structure PairMap (P₁ : TopPair) (P₂ : TopPair) extends C(P₁.total, P₂.total) where
  sub_map : P₁.sub → P₂.sub
  comm : toFun ∘ P₁.map = P₂.map ∘ sub_map

namespace PairMap
variable {P P₁ P₂ P₃ : TopPair}
open TopPair

def ContinuousMapExtendsToPairMap (f : C(P₁.total, P₂.total)) : Prop :=
  ∃ g : P₁.sub → P₂.sub, f ∘ P₁.map = P₂.map ∘ g

@[continuity] -- this does not work
lemma continuous_sub_map (f : PairMap P₁ P₂) : Continuous f.sub_map := by
  apply (Embedding.continuous_iff P₂.isEmbedding).mpr
  rw [← f.comm]
  exact Continuous.comp (by continuity) (Embedding.continuous P₁.isEmbedding)

lemma sub_map_unique {f f' : PairMap P₁ P₂} (h : f.toFun = f'.toFun) : f.sub_map = f'.sub_map := by
  ext x
  have : (f.toFun ∘ P₁.map) x = (f'.toFun ∘ P₁.map) x := by simp only [h]
  rw [f.comm, f'.comm] at this
  apply P₂.isEmbedding.inj this

lemma sub_map_unique' {f f': C(P₁.total, P₂.total)} (h : f = f') (hf : ContinuousMapExtendsToPairMap f) (hf' : ContinuousMapExtendsToPairMap f') : choose hf = choose hf' := by
  ext x
  have : (P₂.map ∘ choose hf) x = (P₂.map ∘ choose hf') x := by
    rw [← choose_spec hf, ← choose_spec hf', h]
  exact P₂.isEmbedding.inj this

lemma sub_map_unique'' {f₁: C(P₁.total, P₂.total)} {f₂ : PairMap P₁ P₂} (h : f₁ = f₂.toFun) (hf : ContinuousMapExtendsToPairMap f₁) : choose hf = f₂.sub_map := by
  ext x
  have : (P₂.map ∘ choose hf) x = (P₂.map ∘ f₂.sub_map) x := by
    rw [← choose_spec hf, h]
    apply congrFun f₂.comm
  exact P₂.isEmbedding.inj this

lemma pair_map_extend_to_pair_map (f : PairMap P₁ P₂) : ContinuousMapExtendsToPairMap f.toContinuousMap := ⟨f.sub_map, f.comm⟩

instance PairMapContinuousMapClass : ContinuousMapClass (PairMap P₁ P₂) P₁.total P₂.total where
  coe := fun f ↦ f.toFun
  coe_injective' := by
    intro f f' h
    ext1
    exact h
    exact sub_map_unique h
  map_continuous := fun f ↦ f.continuous

@[simp]
lemma coe_eq_toFun (f : PairMap P₁ P₂) : ↑f = f.toFun := rfl

@[simp]
lemma toCont_toFun_eq_toFun (f : PairMap P₁ P₂) : f.toContinuousMap.toFun = f.toFun := rfl

@[simp]
lemma toCont_toFun_eq_toFun' (f : PairMap P₁ P₂) : ContinuousMap.toFun f.toContinuousMap = f.toFun := rfl

@[simp]
lemma comm_element (f : PairMap P₁ P₂) : ∀ b, f (P₁.map b) = P₂.map (f.sub_map b) := by
  intro b
  calc f (P₁.map b) = (f ∘ P₁.map) b := rfl
  _ = (P₂.map ∘ f.sub_map) b := by simp only [coe_eq_toFun, f.comm]
  _ = P₂.map (f.sub_map b) := rfl

@[simp]
lemma image_sub (f : PairMap P₁ P₂) : ∀ b : P₁.sub, ∃ b' : P₂.sub, P₂.map b' = f (P₁.map b) := fun b ↦ ⟨f.sub_map b, (comm_element f b).symm⟩

-- yes
protected def id (P : TopPair): PairMap P P where
  toFun := id
  continuous_toFun := by continuity
  sub_map := id
  comm := by simp

@[simp]
lemma id_toFun_eq_id {P: TopPair}: (PairMap.id P).toFun = id := by rfl

@[simp]
lemma id_sub_map_eq_id {P: TopPair}: (PairMap.id P).sub_map = id := by rfl

@[simp]
lemma coe_comp_toFun (f : PairMap P₁ P₂) (g : PairMap P₂ P₃) : (ContinuousMap.mk (↑g ∘ ↑f)).toFun = g ∘ f := by simp

open Set in
protected def comp (f : PairMap P₁ P₂) (g : PairMap P₂ P₃) : PairMap P₁ P₃ where
  toFun := g.toFun ∘ f.toFun
  continuous_toFun := by continuity
  sub_map := g.sub_map ∘ f.sub_map
  comm := by
    simp only [coe_comp_toFun]
    calc (↑g ∘ ↑f) ∘ P₁.map = ↑g ∘ (↑f ∘ P₁.map) := rfl
      _ = ↑g ∘ (P₂.map ∘ f.sub_map) := by simp only [coe_eq_toFun, f.comm]
      _ = (↑g ∘ P₂.map) ∘ f.sub_map := rfl
      _ = (P₃.map ∘ g.sub_map) ∘ f.sub_map := by simp only [coe_eq_toFun, g.comm]

infixr:200 " ◾ "  => PairMap.comp

@[ext]
lemma pairmap_eq_iff_toFun_eq {f g: PairMap P₁ P₂} (h : f.toFun = g.toFun) : f = g := by
  ext1
  exact h
  exact sub_map_unique h

@[simp]
lemma comp_toFun_eq_toFun_comp {f : PairMap P₁ P₂} {g : PairMap P₂ P₃}  : .(f ◾ g).toFun = g.toFun ∘ f.toFun := by rfl

@[simp]
lemma comp_submap_eq_sub_map_comp {f : PairMap P₁ P₂} {g : PairMap P₂ P₃}  : (f ◾ g).sub_map = g.sub_map ∘ f.sub_map := by rfl


@[simp]
theorem comp_id (f: PairMap P₁ P₂) : PairMap.comp f (PairMap.id P₂) = f := by
  apply pairmap_eq_iff_toFun_eq
  simp only [comp_toFun_eq_toFun_comp, id_toFun_eq_id]
  simp only [ContinuousMap.toFun_eq_coe, Function.comp.left_id]


@[simp]
theorem id_comp (f : PairMap P₁ P₂) : PairMap.comp (PairMap.id P₁) f = f := by
  apply pairmap_eq_iff_toFun_eq
  simp only [comp_toFun_eq_toFun_comp, id_toFun_eq_id]
  simp only [ContinuousMap.toFun_eq_coe, Function.comp.right_id]

@[simp]
theorem comp_assoc {P₄ : TopPair} (f : PairMap P₁ P₂) (g : PairMap P₂ P₃) (h : PairMap P₃ P₄) :
  PairMap.comp (PairMap.comp f g) h = PairMap.comp f (PairMap.comp g h) := by
  apply pairmap_eq_iff_toFun_eq
  simp only [comp_toFun_eq_toFun_comp]
  rfl

end PairMap

instance TopPairCategory : Category TopPair where
  Hom P Q := PairMap P Q
  id _ := PairMap.id _
  comp f g := PairMap.comp f g
  id_comp _ := by simp
  comp_id _ := by simp
  assoc _ _ _ := by simp

instance PairMapContinuousMapClass' {P₁ P₂ : TopPair} : ContinuousMapClass (P₁ ⟶ P₂) P₁.total P₂.total := PairMap.PairMapContinuousMapClass

namespace TopPairCategory
variable {P P₁ P₂ P₃ : TopPair}

lemma id_eq_pairmap_id {P : TopPair} : 𝟙 P = PairMap.id P := rfl

lemma comp_eq_pairmap_comp {P₁ P₂ P₃ : TopPair} {f : P₁ ⟶ P₂} {g : P₂ ⟶ P₃} : f ≫ g = PairMap.comp f g := rfl

@[ext]
lemma pairmap_eq_iff_toFun_eq' {f g: P₁ ⟶ P₂} (h : f.toFun = g.toFun) : f = g := PairMap.pairmap_eq_iff_toFun_eq h
end TopPairCategory

namespace PairMap
open PairMap TopPair
variable {P P₁ P₂ P₃ : TopPair}

@[simp]
lemma comp_toFun_eq_toFun_comp' {f : P₁ ⟶ P₂} {g : P₂ ⟶ P₃}  : .(f ≫ g).toFun = g.toFun ∘ f.toFun := by rfl

@[simp]
lemma comp_submap_eq_sub_map_comp' {f : P₁ ⟶ P₂} {g : P₂ ⟶ P₃}  : (f ≫ g).sub_map = g.sub_map ∘ f.sub_map := by rfl

section
def ProjPairMap (P : TopPair) : P(P.total) ⟶ P where
  toFun := id
  continuous_toFun := continuous_id
  sub_map := Empty.rec
  comm := by ext x; exact Empty.rec x

def IncPairMap (P : TopPair) : P(P.sub) ⟶ P(P.total) where
  toFun := P.map
  continuous_toFun := Embedding.continuous P.isEmbedding
  sub_map := Empty.rec
  comm := by simp

@[simp]
lemma inc_pair_map_to_fun_eq_pair_emb {P : TopPair}: (IncPairMap P).toFun = P.map := rfl

@[simp]
lemma inc_pair_map_self_to_fun_eq_id {α : Type} [TopologicalSpace α]: (IncPairMap (toPair₂ α)).toFun = id := rfl


end
-- A pair map induces a map between the subspaces

-- If f : P ⟶ P' and P'.sub is empty then P must be empty

lemma target_sub_empty_of_source_sub_empty (f : PairMap P₁ P₂) (h : IsEmpty P₂.sub) : IsEmpty P₁.sub := by
  by_contra h'
  simp at h'
  obtain ⟨a, _⟩ := image_sub f (Classical.choice h')
  exact h.false a

def PairMapToSubPairMap (f : P₁ ⟶ P₂) : P(P₁.sub) ⟶ P(P₂.sub) where
  toFun := f.sub_map
  continuous_toFun := f.continuous_sub_map -- (by continuity does not work)
  sub_map := Empty.rec
  comm := by simp

@[simp]
lemma to_sub_pair_map_eq_sub_map {f : P₁ ⟶  P₂} : (PairMapToSubPairMap f).toFun = f.sub_map := rfl

@[simp]
lemma id_to_sub_pair_map_eq_id : PairMapToSubPairMap (𝟙 P) = 𝟙 (toPair P.sub) := by
  ext x
  simp at x
  simp only [to_pair_total_eq_self, TopPairCategory.id_eq_pairmap_id, to_sub_pair_map_eq_sub_map,
    id_sub_map_eq_id, id_eq, id_toFun_eq_id]

@[simp]
lemma to_sub_pair_map_comp {f : P₁ ⟶ P₂} {g : P₂ ⟶ P₃} : PairMapToSubPairMap (f ≫  g) = PairMapToSubPairMap f ≫ PairMapToSubPairMap g := by
  ext x
  simp only [to_pair_total_eq_self, TopPairCategory.comp_eq_pairmap_comp,
    to_sub_pair_map_eq_sub_map, comp_submap_eq_sub_map_comp, Function.comp_apply,
    comp_toFun_eq_toFun_comp]

def toPairMap {α β : Type} [TopologicalSpace α] [TopologicalSpace β] (f : C(α, β)):  P(α) ⟶ P(β) where
  toFun := f
  continuous_toFun := by continuity
  sub_map := Empty.rec
  comm := by simp

variable {α β γ: Type} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ] {f: C(α, β)} {g : C(β, γ)}

@[simp]
lemma to_pair_map_to_fun_eq_self : (toPairMap f).toFun = f := rfl

@[simp]
lemma to_pair_map_to_fun_eq_self' : (toPairMap f).toContinuousMap = f := rfl

@[simp]
lemma to_pair_map_to_fun_eq_self'' : (toPairMap f).toContinuousMap.toFun = f := rfl

lemma to_pair_map_comp : (toPairMap f) ≫ (toPairMap g) = toPairMap (ContinuousMap.mk (g ∘ f)) := by
  ext x
  simp
  rfl

section Excision
variable {U : Set P.sub}

lemma excision_is_in (x : (Uᶜ : Set P.sub)) : P.map (x : P.sub)  ∈ (P.map '' U)ᶜ := by
  intro h
  obtain ⟨x', hx'1, hx'2⟩ := h
  apply @(P.isEmbedding.inj) at hx'2
  have : (x : P.sub) ∈ Uᶜ := x.2
  rw [← hx'2] at this
  exact this hx'1


def Excision (P : TopPair) (U : Set P.sub) : TopPair where
  total :=  ((P.map '' U)ᶜ : Set P.total)
  sub :=  (Uᶜ : Set P.sub)
  isTotalTopologicalSpace := by infer_instance
  isSubTopologicalSpace := by infer_instance
  map := fun x ↦ (⟨P.map x, excision_is_in x⟩ : ((P.map '' U)ᶜ : Set P.total))
  isEmbedding := by
    simp [embedding_iff, Function.Injective]
    constructor
    . apply Inducing.codRestrict
      have : (fun x : (Uᶜ : Set P.sub) ↦ P.map x.1) = (fun x ↦ P.map x) ∘ (fun x : (Uᶜ : Set P.sub) ↦ x.1) := by ext; simp
      rw [this]
      apply Inducing.comp P.isEmbedding.toInducing inducing_subtype_val
    . intro _ _ _ _ hab
      apply P.isEmbedding.inj hab


@[simp]
lemma excision_map_eq_self_map {x : (Uᶜ : Set P.sub)}: ((Excision P U).map x).1 = P.map x.1 := rfl

@[simp]
lemma excision_total_eq_total_excision : (Excision P U).total = ((P.map '' U)ᶜ : Set P.total) := rfl

@[simp]
lemma excision_sub_eq_sub_excision : (Excision P U).sub = (Uᶜ : Set P.sub) := rfl

def ExcisionInc (P : TopPair) (U : Set P.sub) : (Excision P U) ⟶ P where
  toFun := fun x ↦ x.1
  continuous_toFun := by continuity
  sub_map := fun x ↦ x.1
  comm := by ext; simp

end Excision

section PairHomotopy
variable {P₁ P₂ : TopPair}
open ContinuousMap

structure PairHomotopy (f₀ f₁ : PairMap P₁ P₂) extends HomotopyWith (f₀ : C(P₁.total, P₂.total)) f₁ ContinuousMapExtendsToPairMap

def PairHomotopic (f₀ f₁ : PairMap P₁ P₂) : Prop :=
  Nonempty (PairHomotopy f₀ f₁)

infixl:25 " ≃ₕ " => PairMap.PairHomotopic

@[ext]
structure PairHomotopyEquiv (P₁ : TopPair) (P₂ : TopPair) where
  toFun : P₁ ⟶ P₂
  invFun : P₂ ⟶ P₁
  left_inv : PairHomotopic (toFun ≫ invFun) (𝟙 P₁)
  right_inv : PairHomotopic (invFun ≫ toFun) (𝟙 P₂)

infixl:25 " ≃ₕ " => PairMap.PairHomotopyEquiv

variable {P₁ P₂ : TopPair}
class IsPairHomotopyEquiv (f : P₁ ⟶ P₂) : Prop where
  out : ∃inv : P₂ ⟶ P₁, ((f ≫ inv) ≃ₕ (𝟙 P₁)) ∧ ((inv ≫ f) ≃ₕ (𝟙 P₂))

instance PairHomotopyEquivToFunIsPairHomotopyEquiv (htp : P₁ ≃ₕ P₂) : IsPairHomotopyEquiv htp.toFun := ⟨htp.invFun, ⟨htp.left_inv, htp.right_inv⟩⟩

instance PairHomotopyEquivInvFunIsPairHomotopyEquiv  (htp : P₁ ≃ₕ P₂) : IsPairHomotopyEquiv htp.invFun := ⟨htp.toFun, ⟨htp.right_inv, htp.left_inv⟩⟩

noncomputable def inv (f : P₁ ⟶ P₂) [htp : IsPairHomotopyEquiv f] : P₂ ⟶ P₁ :=
  Classical.choose htp.out

@[simp]
theorem hom_inv_id (f : P₁ ⟶ P₂) [htp : IsPairHomotopyEquiv f] : f ≫ inv f ≃ₕ 𝟙 P₁ :=
  (Classical.choose_spec htp.out).left

@[simp]
theorem inv_hom_id (f : P₁ ⟶ P₂) [htp : IsPairHomotopyEquiv f] : inv f ≫ f ≃ₕ 𝟙 P₂ :=
  (Classical.choose_spec htp.1).right


open TopPair
-- toPair induces a PairMap
variable {P₁ P₂ : TopPair}
variable (f₂ : P₁ ⟶ P₂)
def PairHomotopyToPairTotal (f₁ f₂ : P₁ ⟶ P₂) (htp : PairHomotopy f₁ f₂) : PairHomotopy (toPairMap f₁.toContinuousMap) (toPairMap f₂.toContinuousMap) where
  toFun := htp.toFun
  continuous_toFun := htp.continuous_toFun
  map_zero_left := htp.map_zero_left
  map_one_left := htp.map_one_left
  prop' := by
    simp
    intro _ _
    exact ⟨Empty.rec, by simp⟩

def PairHomotopicToPairTotal (f₁ f₂ : P₁ ⟶ P₂) (htp : PairHomotopic f₁ f₂) : (toPairMap f₁.toContinuousMap) ≃ₕ (toPairMap f₂.toContinuousMap) := by
  dsimp [PairHomotopic]
  by_contra h
  simp at h
  exact h.elim <| PairHomotopyToPairTotal f₁ f₂ (Classical.choice htp)

def HomotopyEquivToPairTotal (f : P₁ ⟶ P₂) [htp : IsPairHomotopyEquiv f] : toPair P₁.total ≃ₕ toPair P₂.total where
  toFun := toPairMap f
  invFun := toPairMap (inv f)
  left_inv := by
    rw [to_pair_map_comp]
    have : 𝟙 (toPair P₁.total) = toPairMap (𝟙 P₁) := by ext; simp; rfl
    rw [this]
    exact PairHomotopicToPairTotal (f ≫ inv f) (𝟙 P₁) (hom_inv_id f)
  right_inv := by
    rw [to_pair_map_comp]
    have : 𝟙 (toPair P₂.total) = toPairMap (𝟙 P₂) := by ext; simp; rfl
    rw [this]
    exact PairHomotopicToPairTotal (inv f ≫ f) (𝟙 P₂) (inv_hom_id f)

instance IsHomotopyEquivToPairTotal (f : P₁ ⟶ P₂) [IsPairHomotopyEquiv f] : IsPairHomotopyEquiv (toPairMap f.toContinuousMap) := PairHomotopyEquivToFunIsPairHomotopyEquiv (HomotopyEquivToPairTotal f)

def PairHomotopyToPairSub (f₁ f₂ : P₁ ⟶ P₂) (htp : PairHomotopy f₁ f₂) : PairHomotopy (PairMapToSubPairMap f₁) (PairMapToSubPairMap f₂) where
  toFun := fun (i, x) ↦ choose (htp.prop' i) x
  continuous_toFun := by
    have aux : htp.toFun ∘  (fun (i,x) ↦ (i, P₁.map x)) = P₂.map ∘ (fun (i, x) ↦ choose (htp.prop' i) x) := by
      ext x
      exact congrFun (choose_spec (htp.prop' x.1)) x.2
    have : Continuous (htp.toFun ∘  (fun (i,x) ↦ (i, P₁.map x))) := by
      apply Continuous.comp htp.continuous_toFun
      simp
      exact ⟨by continuity, Continuous.snd' <| Embedding.continuous P₁.isEmbedding⟩
    rw [aux] at this
    apply (Embedding.continuous_iff P₂.isEmbedding).mpr this
  map_zero_left := by
    intro x
    simp
    apply congrFun
    -- have : (fun x ↦ (PairMapToSubPairMap f₁) x) = f₁.sub_map := rfl
    simp [htp.map_zero_left]
    set g := choose (_ : ∃ x, (fun g ↦ (fun x ↦ f₁ x) ∘ P₁.map = P₂.map ∘ g) x)
    have : g = f₁.sub_map := by
      apply sub_map_unique'' rfl
    exact this
  map_one_left := by
    intro x
    simp
    apply congrFun
    -- have : (fun x ↦ (PairMapToSubPairMap f₁) x) = f₁.sub_map := rfl
    simp [htp.map_one_left]
    set g := choose (_ : ∃ x, (fun x ↦ (fun x ↦ f₂ x) ∘ P₁.map = P₂.map ∘ x) x)
    have : g = f₂.sub_map := by
      apply sub_map_unique'' rfl
    exact this
  prop' := by
    simp
    intro _ _
    exact ⟨Empty.rec, by simp⟩

def PairHomotopicToPairSub (f₁ f₂ : P₁ ⟶ P₂) (htp : PairHomotopic f₁ f₂) : (PairMapToSubPairMap f₁) ≃ₕ (PairMapToSubPairMap f₂) := by
  dsimp [PairHomotopic]
  by_contra h
  simp at h
  exact h.elim <| PairHomotopyToPairSub f₁ f₂ (Classical.choice htp)

def HomotopyEquivToPairSub (f : P₁ ⟶ P₂) [htp : IsPairHomotopyEquiv f] : toPair P₁.sub ≃ₕ toPair P₂.sub where
  toFun := PairMapToSubPairMap f
  invFun := PairMapToSubPairMap (inv f)
  left_inv := by
    rw [← to_sub_pair_map_comp]
    have : 𝟙 (toPair P₁.sub) = PairMapToSubPairMap (𝟙 P₁) := by ext; simp;
    rw [this]
    exact PairHomotopicToPairSub (f ≫ inv f) (𝟙 P₁) (hom_inv_id f)
  right_inv := by
    rw [← to_sub_pair_map_comp]
    have : 𝟙 (toPair P₂.sub) = PairMapToSubPairMap (𝟙 P₂) := by ext; simp;
    rw [this]
    exact PairHomotopicToPairSub (inv f ≫ f) (𝟙 P₂) (inv_hom_id f)

instance IsHomotopyEquivToPairSub (f : P₁ ⟶ P₂) [IsPairHomotopyEquiv f] : IsPairHomotopyEquiv (PairMapToSubPairMap f) := PairHomotopyEquivToFunIsPairHomotopyEquiv (HomotopyEquivToPairSub f)

end PairHomotopy
end PairMap

namespace Homology
variable {R : Type*} [Ring R]
variable {P : TopPair} {P' : TopPair}
open PairMap TopPair
open Function

section Homotopy_invariance
class HomotopyInvariant (F : TopPair ⥤ ModuleCat R) : Prop :=
  homotopy_inv {P P' : TopPair} {f f' : P ⟶ P'}: f ≃ₕ f' → (F.map f = F.map f')

variable {F : TopPair ⥤ ModuleCat R} [h : HomotopyInvariant F]
-- Send homotopy equivalence to isomorphism

lemma homotopy_inv_of_induce_eq {P P' : TopPair} {f f' : P ⟶ P'}: f ≃ₕ f' → (F.map f = F.map f') := h.homotopy_inv

lemma homotopy_inv_id_to_id {f : P ⟶ P} (htp : f ≃ₕ (𝟙 P)) : F.map f = 𝟙 (F.obj P) := by
  rw [← F.map_id]
  apply h.homotopy_inv
  exact htp

instance homotopy_inv_equi_of_iso {f : P ⟶ P'} [htp : IsPairHomotopyEquiv f] : IsIso (F.map f) where
  out := by
    use F.map (inv f)
    repeat rw [← F.map_comp, TopPairCategory.comp_eq_pairmap_comp]
    exact ⟨homotopy_inv_id_to_id <| hom_inv_id f, homotopy_inv_id_to_id <| inv_hom_id f⟩

end Homotopy_invariance

section Excisive

/-
  Excisive
-/

class Excisive {R : Type*} [Ring R] (F : TopPair ⥤ ModuleCat R) : Prop :=
  excisive : ∀ P, ∀ U : Set (P.sub), IsIso (F.map (ExcisionInc P U))

lemma excisive_of_induce_iso {R : Type*} [Ring R] (F : TopPair ⥤ ModuleCat R) [h : Excisive F] {P : TopPair} {U : Set (P.sub)} : IsIso (F.map (ExcisionInc P U)) := h.excisive P U

end Excisive

section Additive

/-
  additivity
-/

def SigmaTopPair {ι : Type} (P : ι → TopPair) : TopPair where
  total := Σ i, (P i).total
  sub :=  Σ i, (P i).sub
  isTotalTopologicalSpace := by infer_instance
  isSubTopologicalSpace := by infer_instance
  map := Sigma.map id (fun i a ↦ (@TopPair.map (P i)) a)
  isEmbedding := by
    simp [embedding_iff]
    have : Function.Injective (@id ι) := by simp [Function.Injective]
    constructor
    . apply (inducing_sigma_map this).mpr
      exact fun i ↦ (P i).isEmbedding.toInducing
    . apply Function.Injective.sigma_map this
      exact fun i ↦ (P i).isEmbedding.inj

def SigmaTopPairInc {ι : Type} (P : ι → TopPair) (i : ι) : PairMap (P i) (SigmaTopPair P) where
  toFun := fun a ↦ ⟨i, a⟩
  continuous_toFun := continuous_iSup_rng continuous_coinduced_rng
  sub_map := fun a ↦ ⟨i, a⟩
  comm := by ext x; simp [SigmaTopPair, Sigma.map_mk]


class Additive {R : Type*} [Ring R] (F : TopPair ⥤ ModuleCat R) : Prop :=
  additivity {ι : Type} {P : ι → TopPair} {i : ι} : IsIso (F.map (SigmaTopPairInc P i))

lemma additive_of_sigma_inc_induce_iso {R : Type*} [Ring R] (F : TopPair ⥤ ModuleCat R) [add : Additive F] {ι : Type} {P : ι → TopPair} {i : ι}: IsIso (F.map (SigmaTopPairInc P i)) := add.additivity

end Additive

section Boundary_opeartor
-- an endofunctor of TopPair ` (α , β) ↦ (β, ∅)
-- def PairToSubFunctor.{u₁, u₂} : TopPair.{u₁, u₂} ⥤ TopPair.{u₂, 0} where
def PairToSubFunctor : TopPair ⥤ TopPair where
  obj P := toPair P.sub
  map := PairMapToSubPairMap
  map_id := @id_to_sub_pair_map_eq_id
  map_comp := @to_sub_pair_map_comp

abbrev BoundaryOp (F : TopPair ⥤ ModuleCat R) (G : TopPair ⥤ ModuleCat R) := NatTrans F (PairToSubFunctor ⋙ G)
end Boundary_opeartor


structure InjProjExact (F : TopPair ⥤ ModuleCat R) (P : TopPair) : Prop where
  inj_proj_exact : Function.Exact (F.map (IncPairMap P)) (F.map (ProjPairMap P))

structure ProjBoundExact {F G : TopPair ⥤ ModuleCat R} (bd :BoundaryOp F G) (P : TopPair) : Prop where
  proj_bound_exact : Function.Exact (F.map (ProjPairMap P)) (bd.app P)

structure BoundInjExact {F G : TopPair ⥤ ModuleCat R} (bd :BoundaryOp F G) (P : TopPair) : Prop where
  bound_inj_exact : Function.Exact (bd.app P) (G.map (IncPairMap P))

structure ExOrdHomology (R : Type*) [Ring R] where
  homology (n : ℤ): TopPair ⥤ ModuleCat R
  homotopy_inv : ∀ n,  HomotopyInvariant (homology n)
  excisive : ∀ n, Excisive (homology n)
  additive : ∀ n, Additive (homology n)
  boundary_op (n : ℤ) : BoundaryOp (homology n) (homology (n-1))
  exact_seq_inj_proj : ∀ n, ∀ P, InjProjExact (homology n) P
  exact_seq_proj_bound : ∀ n, ∀ P, ProjBoundExact (boundary_op n) P
  exact_seq_bound_inj : ∀ n, ∀ P, BoundInjExact (boundary_op n) P

attribute [instance] ExOrdHomology.homotopy_inv ExOrdHomology.excisive ExOrdHomology.additive

structure OrdHomology (R : Type*) [Ring R] extends ExOrdHomology R where
  dimension (n : ℤ) (α β: Type) [Unique α] [TopologicalSpace α]: n ≠ 0 → Subsingleton ((homology n).obj (toPair α))



end Homology


section Basic_results_of_homology
namespace Homology
open Homology TopPair PairMap TopPairCategory

variable {R : Type*} [Ring R]

section Extraordinary
variable {H : ExOrdHomology R}

/-
  If the embedding `A → X` of `(X, A)` induces an iso on each `Hₖ` then `Hₖ(X,A)=0`
-/
def EmbeddingInduceIso (P : TopPair) (H : ExOrdHomology R) : Prop := ∀ k, IsIso ((H.homology k).map (IncPairMap P))

lemma inclusion_induce_iso_of_homology_trivial {P : TopPair} (h : EmbeddingInduceIso P H) : ∀ k, Subsingleton ((H.homology k).obj P) :=
  fun k ↦ exact_iso_iso_of_subsingleton (H.exact_seq_inj_proj k P).inj_proj_exact (H.exact_seq_proj_bound k P).proj_bound_exact (H.exact_seq_bound_inj k P).bound_inj_exact (h k) (h <| k - 1)

instance toPair₂_inc_pair_map_iso {α : Type} [TopologicalSpace α] : IsIso (IncPairMap (toPair₂ α)) := by
  use IncPairMap (toPair₂ α)
  constructor
  . ext1
    simp only [comp_eq_pairmap_comp, comp_toFun_eq_toFun_comp, inc_pair_map_self_to_fun_eq_id, to_pair'_sub_eq_self, to_pair'_total_eq_self, Function.comp.right_id, id_eq_pairmap_id, id_toFun_eq_id]
  . ext1
    simp only [to_pair'_total_eq_self, to_pair'_sub_eq_self, comp_eq_pairmap_comp, comp_toFun_eq_toFun_comp, id_eq_pairmap_id, inc_pair_map_self_to_fun_eq_id, Function.comp.right_id, id_toFun_eq_id]

/--
  `h_k(X,X)` is zero everywhere
-/
lemma toPair₂_trivial_homology {α : Type} [TopologicalSpace α] : ∀ k, Subsingleton ((H.homology k).obj (toPair₂ α)) := by
  apply inclusion_induce_iso_of_homology_trivial
  dsimp [EmbeddingInduceIso]
  intro k
  apply Functor.map_isIso

/--
  If `(X,A)` is pair homotopic to point `(a, a)`, then `A ↪ X` induces isomorphism on homology everywhere.
-/
lemma pair_homotopic_points_of_inc_induce_iso {P : TopPair} {α : Type} [TopologicalSpace α] [Unique α] (f: P ⟶ toPair₂ α) [IsPairHomotopyEquiv f] : EmbeddingInduceIso P H := by
  intro k
  set f₁ := toPairMap f.toContinuousMap
  set f₂ := PairMapToSubPairMap f
  have : IncPairMap P ≫ f₁ = f₂ ≫ (IncPairMap <| toPair₂ α) := by
    ext1
    simp only [to_pair_total_eq_self, to_pair'_total_eq_self, comp_eq_pairmap_comp, comp_toFun_eq_toFun_comp, inc_pair_map_to_fun_eq_pair_emb, to_pair'_sub_eq_self]
    repeat rw [to_pair_map_to_fun_eq_self']
    simp only [to_pair'_map_eq_id, to_pair'_sub_eq_self]
    ext x
    have : Subsingleton (toPair₂ α).total := by simp; infer_instance
    apply (eq_iff_true_of_subsingleton ((f.toFun ∘ P.map) x) ((id ∘ f.sub_map) x)).mpr trivial
  have aux := congrArg (H.homology k).map this
  repeat rw [(H.homology k).map_comp] at aux
  have : IsIso <| (ExOrdHomology.homology H k).map (IncPairMap P) ≫ (ExOrdHomology.homology H k).map f₁ := by
    rw [aux]
    apply IsIso.comp_isIso
  apply IsIso.of_isIso_comp_right ((ExOrdHomology.homology H k).map (IncPairMap P)) ((ExOrdHomology.homology H k).map f₁)


lemma pair_homotopic_points_of_homology_trivial (H : ExOrdHomology R) {P : TopPair} {α : Type} [TopologicalSpace α] [Unique α] (htp : P ≃ₕ toPair₂ α) : ∀ k, Subsingleton ((H.homology k).obj P) :=
  inclusion_induce_iso_of_homology_trivial <| pair_homotopic_points_of_inc_induce_iso htp.toFun


/--
  If `A` of `(X, A)` has zero homology at `k` and `k-1`, then the projection induces an isomorphism `h_k(X) → h_k(X,A)`
-/
lemma pair_zero_homology_of_proj_induce_iso {P : TopPair} (k : ℤ) (h₁ : Subsingleton <| (H.homology k).obj <| toPair P.sub) (h₂ : Subsingleton <| (H.homology (k-1)).obj <| toPair P.sub) : IsIso <| (H.homology k).map <| ProjPairMap P:= exact_subsingleton_subsingleton_of_isiso (H.exact_seq_inj_proj k P).inj_proj_exact (H.exact_seq_proj_bound k P).proj_bound_exact h₁ h₂


/--
  If `X` of `(X, A)` has zero homology at `k` and `k-1`, then the boundary operator `h_k(X,A) → H_{k-1}(A)` is an isomorphism
-/
lemma pair_zero_homology_of_boundary_op_iso {P : TopPair} (k : ℤ) (h₁ : Subsingleton <| (H.homology k).obj <| toPair P.total) (h₂ : Subsingleton <| (H.homology (k-1)).obj <| toPair P.total) : IsIso <| (H.boundary_op k).app P := exact_subsingleton_subsingleton_of_isiso (H.exact_seq_proj_bound k P).proj_bound_exact (H.exact_seq_bound_inj k P).bound_inj_exact h₁ h₂

end Extraordinary

end Homology
end Basic_results_of_homology


section Long_exact_sequence_of_triple
namespace TopPair
structure TopTriple where
  total : Type
  isTotalTopologicalSpace : TopologicalSpace total
  sub₁ : Set total
  sub₂ : Set total
  inc : sub₂ ⊆ sub₁

attribute [instance] TopTriple.isTotalTopologicalSpace

end TopPair

namespace Homology
open TopPair PairMap Homology
variable (T : TopTriple)

def TripleInc₁ : Pᵢ(T.inc) ⟶ P(T.total, T.sub₂) where
  toFun x := x.1
  continuous_toFun := by continuity
  sub_map := id
  comm := by ext; simp

def TripleInc₂ : P(T.total, T.sub₂) ⟶ P(T.total, T.sub₁) where
  toFun := id
  continuous_toFun := by continuity
  sub_map x := ⟨x.1, T.inc x.2⟩
  comm := by ext; simp

variable {R : Type*} [Ring R] (H : ExOrdHomology R) (k : ℤ)

def TripleBoundaryOp : (H.homology k).obj P(T.total, T.sub₁) ⟶ (H.homology <| k-1).obj Pᵢ(T.inc) := ((H.boundary_op k).app P(T.total, T.sub₁)) ≫ ((H.homology (k-1)).map <| ProjPairMap Pᵢ(T.inc))

lemma triple_exact_inc₁_inc₂ : Function.Exact ((H.homology k).map <| TripleInc₁ T)  ((H.homology k).map <| TripleInc₂ T) := sorry

lemma triple_exact_inc₂_boundary : Function.Exact ((H.homology k).map <| TripleInc₂ T) (TripleBoundaryOp T H k) := sorry

lemma triple_exact__boundary_inc₁ : Function.Exact (TripleBoundaryOp T H k) ((H.homology <| k-1).map <| TripleInc₁ T):= sorry

/--
  For a triple `(α, β, γ)`, if `(α, γ)` is homotopic to `(*, *)`, then `h_{k+1}(α, β) → h_k(β, γ)` is an isomorphism everywhere
-/
lemma triple_pair_homotopic_points_of_boundary_isiso {σ : Type} [TopologicalSpace σ] [Unique σ] (htp : P(T.total, T.sub₂) ≃ₕ toPair₂ σ) {k : ℤ} : IsIso (TripleBoundaryOp T H k) := by
  have h₁ := pair_homotopic_points_of_homology_trivial H htp k
  have h₂ := pair_homotopic_points_of_homology_trivial H htp (k-1)
  have e₁ := triple_exact_inc₂_boundary T H k
  have e₂ := triple_exact__boundary_inc₁ T H k
  apply exact_subsingleton_subsingleton_of_isiso e₁ e₂ h₁ h₂

end Homology
end Long_exact_sequence_of_triple

namespace TopologicalSimplex
open SimplexCategory Simplicial BigOperators Set TopPair PairMap Homology

scoped[TopologicalSimplex] notation  "Δ("n")" => toTopObj [n]

@[ext]
structure DownwardClosed (n : ℕ) where
  carrier : Set (Set (Fin (n + 1)))
  downward_closed : ∀ I J, J ∈ carrier ∧ I.Nonempty ∧ I ⊆ J → I ∈ carrier

instance (n : ℕ) : SetLike (DownwardClosed n)  (Set (Fin (n + 1))) where
  coe s := s.carrier
  coe_injective' := by intro _ _ h; ext1; exact h

-- Col for collection
def BoundaryCol (n : ℕ) : DownwardClosed n where
  carrier := {I | I.Nonempty ∧ I ≠ univ}
  downward_closed := by
    intro I J h
    constructor
    . exact h.2.1
    . by_contra h'
      rw [h'] at h
      exact h.1.2 <| univ_subset_iff.mp h.2.2

def HornCol (n : ℕ) (i : Fin (n + 1)): DownwardClosed n where
  carrier := {I | I.Nonempty ∧ I ≠ univ ∧ I ≠ {j | j ≠ i }}
  downward_closed := by
    intro I J h
    simp
    simp at h
    constructor
    . exact h.2.1
    . contrapose! h
      intro h1 _ h3
      have : I ≠ univ := by
        by_contra h'
        rw [h'] at h3
        apply h1.2.1 (univ_subset_iff.mp h3)
      specialize h this
      rw [h] at h3
      by_cases hi : i ∈ J
      . refine h1.2.1 (univ_subset_iff.mp ?_)
        intro j _
        by_cases hj : j ≠ i
        exact h3 hj
        simp at hj
        rwa [← hj] at hi
      . refine h1.2.2 (subset_antisymm ?_ h3)
        intro j hj
        simp
        intro h
        apply hi
        rwa [h] at hj

def Realization {n : ℕ} (U : DownwardClosed n) :=
  {f : Δ(n)| { i : Fin (n + 1) | f i ≠ 0 } ∈ U.carrier}

lemma mem_realization_iff {n : ℕ} {U : DownwardClosed n} {f : Δ(n)} : f ∈ Realization U ↔ { i : Fin (n + 1) | f i ≠ 0 } ∈ U.carrier := by simp [Realization]

notation "∂Δ("n")" => Realization (BoundaryCol n)

notation "Λ("n", "i")" => Realization (HornCol n i)

notation "d("n", "i")" => toTopMap (@δ n i)

lemma realization_mono {n : ℕ} {U₁ U₂: DownwardClosed n} (h: U₁.1 ⊆ U₂.1): Realization U₁ ⊆ Realization U₂ := by
  simp only [Realization]
  exact fun _ hf ↦ h hf

lemma sum_eq_one {n : ℕ} (f : Δ(n)) : ∑ i, f i = 1 := by
  simp [toTopObj] at f
  exact f.2

lemma exist_nonzero {n : ℕ} (f : Δ(n)) : ∃ j, f j ≠ 0 := by
  by_contra h
  simp at h
  have : ∑ i, f i = 0 := by
    apply Finset.sum_eq_zero
    simp [h]
  rw [sum_eq_one f] at this
  norm_num at this

lemma le_one {n : ℕ} (f : Δ(n)) (j : Fin (n+1)): (f j : ℝ) ≤ 1 := by
  by_contra h
  push_neg at h
  have : f j ≤ ∑ i, f i := by
    apply Finset.single_le_sum
    exact fun i _ ↦ (f i).2
    exact Fintype.complete j
  rw [sum_eq_one] at this
  have := lt_of_lt_of_le h this
  norm_num at this

lemma horn_sub_boundary {n : ℕ} {i : Fin (n + 1)} : Λ(n, i) ⊆ ∂Δ(n) := by
  apply realization_mono
  have h1 : (HornCol n i).carrier = {I | I.Nonempty ∧ I ≠ univ ∧ I ≠ {j | j ≠ i }} := rfl
  have h2 : (BoundaryCol n).carrier = {I | I.Nonempty ∧ I ≠ univ} := rfl
  simp [h1, h2]
  intro a h h' _
  exact ⟨h, h'⟩

def Horn (n : ℕ) (i : Fin (n + 1)) : Set ∂Δ(n) := {(⟨x.1, horn_sub_boundary x.2⟩ : ∂Δ(n)) | x : Λ(n,i)}

notation "Λ'("n", "i")" => Horn n i

section
variable {n: ℕ} {i: Fin (n + 2)} {x : Δ(n)}
lemma face_map_miss_one_vertex : (d(n,i) x) i = 0 := by
  simp
  exact fun k hk ↦ (Fin.succAbove_ne i k hk).elim

lemma face_map_exist_nonzero : Set.Nonempty {j | (d(n,i) x) j ≠ 0} := by
  obtain ⟨j, hj⟩ := exist_nonzero x
  use (δ i) j -- ` : Fin (n + 2) `
  simp
  use j

lemma face_map_exist_zero : {j | (d(n,i) x) j ≠ 0} ≠ univ := by
  by_contra h
  have : i ∈ {j | (toTopMap (δ i) x) j ≠ 0} := by
    rw [h]; simp
  simp at this
  obtain ⟨j, hj, _⟩ := this
  apply (Fin.succAbove_ne i j) hj

lemma face_map_image_sub_boundary : d(n,i) x ∈ ∂Δ(n+1) := by
  apply mem_realization_iff.mpr
  have : (BoundaryCol (n+1)).carrier = {I | I.Nonempty ∧ I ≠ univ} := rfl
  simp only [this]
  exact ⟨face_map_exist_nonzero, face_map_exist_zero⟩


lemma face_map_image_of_boundary_sub_horn {x : ∂Δ(n)} : d(n,i) x ∈ Λ(n+1, i) := by
  apply mem_realization_iff.mpr
  have : (HornCol (n+1) i).carrier = {I | I.Nonempty ∧ I ≠ univ ∧ I ≠ {j | j ≠ i }} := rfl
  simp only [this]
  refine ⟨face_map_exist_nonzero, ⟨face_map_exist_zero, ?_⟩⟩
  by_contra h
  have aux : ∀ j, j ≠ i → (d(n, i) x) j ≠ 0 := by
    intro j hj
    have : j ∈ {j | j ≠ i} := hj
    rw [← h] at this
    exact this
  have : ∀ (j : Fin (n + 1)), x.1 j ≠ 0 := by
    intro j
    by_contra h
    apply aux ((δ i) j) _ _
    exact Fin.succAbove_ne i j
    simp [toTopMap]
    intro k hk
    apply (Fin.succAboveEmb i).inj' at hk
    rwa [← hk] at h
  have : x.1 ∉ ∂Δ(n) := by
    simp [mem_realization_iff, BoundaryCol]
    intro _
    apply univ_subset_iff.mp
    intro j _
    exact this j
  exact this x.2

end
/--
  vertex of simplexes
-/

def Ver (n : ℕ) (i : Fin (n + 1)) : Δ(n) where
  val := fun k ↦ if k = i then 1 else 0
  property := by simp [toTopObj]

lemma ver_val {n : ℕ} {i : Fin (n + 1)} : (Ver n i).val = fun k ↦ if k = i then 1 else 0 := by
  -- rfl???
  ext j
  simp [Ver]
  -- rfl???
  split_ifs
  rfl
  rfl

@[simp]
lemma ver_app₁ {n : ℕ} {i : Fin (n + 1)} : (Ver n i).val i = 1 := by simp [ver_val]

@[simp]
lemma ver_app₂ {n : ℕ} {i : Fin (n + 1)} {j : Fin (n+1)} (h : j ≠ i): (Ver n i).val j = 0 := by simp [ver_val, h]

lemma vertex_in_boundary {n : ℕ} [NeZero n] {i : Fin (n + 1)} : Ver n i ∈ ∂Δ(n) := by
  simp [mem_realization_iff, BoundaryCol]
  constructor
  . exact ⟨i, by simp [Ver]⟩
  . apply Ne.symm
    apply ne_of_mem_of_not_mem' _ _
    exact (i+1)
    simp
    simp [Ver]
    exact NeZero.ne n

def VerB (n : ℕ) [NeZero n] (i : Fin (n + 1)) : ∂Δ(n) := ⟨Ver n i, vertex_in_boundary⟩

@[simp]
lemma ver_b_val {n : ℕ} [NeZero n] (i : Fin (n + 1)) : (VerB n i).val = Ver n i := rfl

lemma vertex_in_horn {n : ℕ} [NeZero n] {i : Fin (n + 1)}: Ver n i ∈ Λ(n,i) := by
  simp [mem_realization_iff, HornCol]
  constructor
  . use i
    simp [Ver]
  . constructor
    . apply Ne.symm
      apply ne_of_mem_of_not_mem' _ _
      exact (i+1)
      simp
      simp [Ver]
      exact NeZero.ne n
    . apply ne_of_mem_of_not_mem' _ _
      exact i
      simp [Ver]
      simp

def VerH (n : ℕ) [NeZero n] (i : Fin (n + 1)) : Λ(n,i) := ⟨Ver n i, vertex_in_horn⟩

@[simp]
lemma ver_h_val {n : ℕ} [NeZero n] (i : Fin (n + 1)) : (VerH n i).val = Ver n i := rfl

def BoundaryHornExciseVertex (n : ℕ) [NeZero n] (i : Fin (n+1)) := ExcisionInc Pᵢ(horn_sub_boundary) {VerH n i}

variable {n : ℕ} {i : Fin (n+2)} {j : Fin (n+2)}
-- #check Excision P(Δ(n), ∂Δ(n)) {VerB n 0}

lemma face_map_miss_one_vertex' (x : Δ(n)) : (d(n,j) x) ∈ ({Ver (n+1) j}ᶜ : Set Δ(n+1)) := by
  by_contra h
  simp at h
  have : (0 : NNReal) = 1 := by
    calc 0 = (d(n, j) x) j := face_map_miss_one_vertex.symm
    _ = (Ver (n + 1) j) j := by rw [h]
    _ = 1 := by simp [Ver]
  norm_num at this


def FaceMapReduced (n : ℕ) (i : Fin (n+2)): P(Δ(n), ∂Δ(n)) ⟶ (Excision Pᵢ(horn_sub_boundary) {VerH (n+1) i}) where
  toFun :=
    fun x ↦ ⟨⟨d(n,i) x, face_map_image_sub_boundary⟩, by
      simp
      by_contra h
      apply @face_map_miss_one_vertex' n i x
      exact h
    ⟩
  continuous_toFun := by apply Continuous.codRestrict; continuity
  sub_map := fun x ↦ ⟨⟨d(n,i) x.1, face_map_image_of_boundary_sub_horn⟩, by
      simp
      by_contra h
      apply congrArg Subtype.val at h
      simp at h
      apply @face_map_miss_one_vertex' n i x.1
      exact h
    ⟩
  comm := by ext; simp; ext1; simp

def FaceMapPairMap (n : ℕ) (i : Fin (n+2)): P(Δ(n), ∂Δ(n)) ⟶ P(Δ(n+1), ∂Δ(n+1)) where
  toFun := d(n,i)
  continuous_toFun := by continuity
  sub_map := fun x ↦ ⟨d(n,i) x.1, face_map_image_sub_boundary⟩
  comm := by ext; simp

def FaceMapPairMap' (n : ℕ) (i : Fin (n+2)): P(Δ(n), ∂Δ(n)) ⟶ Pᵢ(@horn_sub_boundary (n+1) i) where
  toFun := fun x ↦ ⟨d(n,i) x, face_map_image_sub_boundary⟩
  continuous_toFun := by continuity
  sub_map := fun x ↦ ⟨d(n,i) x.1, face_map_image_of_boundary_sub_horn⟩
  comm := by ext; simp

lemma face_map_decompose_through_reduced_map : FaceMapPairMap' n i = (FaceMapReduced n i) ≫ (BoundaryHornExciseVertex (n+1) i) := by
  simp
  ext
  simp [FaceMapPairMap', FaceMapReduced, BoundaryHornExciseVertex, ExcisionInc]

-- lemma face_map_decompose_through_reduced_map' : (FaceMapPairMap n i : P(Δ(n), ∂Δ(n)) ⟶ P(Δ(n+1), ∂Δ(n+1))) = (FaceMapReduced n i : P(Δ(n), ∂Δ(n)) ⟶ (Excision P(Δ(n+1), ∂Δ(n+1)) {VerB (n+1) i})) ≫ (BoundaryHornExciseVertex (n+1) i) := by simp;

def FaceMapReducedPairHomotopyEquiv: P(Δ(n), ∂Δ(n)) ≃ₕ (Excision Pᵢ(horn_sub_boundary) {VerH (n+1) i}) where
  toFun := FaceMapReduced n i
  invFun := sorry
  left_inv := sorry
  right_inv := sorry

instance FaceMapReducedIsPairHomotopyEquiv : PairMap.IsPairHomotopyEquiv (FaceMapReduced n i) := PairHomotopyEquivToFunIsPairHomotopyEquiv FaceMapReducedPairHomotopyEquiv

end TopologicalSimplex


section Homology_of_Topological_Simplex
namespace TopologicalSimplex

open TopPair Homology TopologicalSimplex

variable {R : Type*} [Ring R]
variable {H : ExOrdHomology R}
variable {n : ℕ} {i : Fin (n+2)}

-- maybe instance?
instance reduced_face_map_induce_iso {k : ℤ}: IsIso ((H.homology k).map (FaceMapReduced n i)) := homotopy_inv_equi_of_iso

instance excision_inc_induce_iso {k : ℤ} : IsIso ((H.homology k).map (BoundaryHornExciseVertex (n+1) i)) := by
  apply excisive_of_induce_iso

instance face_map_induce_is_iso (k : ℤ) : IsIso ((H.homology k).map (FaceMapPairMap' n i)) := by
  rw [face_map_decompose_through_reduced_map, (H.homology k).map_comp]
  apply IsIso.comp_isIso

-- lemma subsingleton_unique_topology {α : Type} (h : Subsingleton α) [t1 : TopologicalSpace α] [t2 : TopologicalSpace α] : t1 = t2 := by simp only [eq_iff_true_of_subsingleton]

def FaceMaoReducedInduceIso (n : ℕ) (i : Fin (n + 1)) (k : ℤ) :(H.homology k).obj P(Δ(n),∂Δ(n)) ≅ (H.homology k).obj Pᵢ(@horn_sub_boundary (n+1) i) where
  hom := (H.homology k).map (FaceMapPairMap' n i)
  inv := CategoryTheory.inv ((H.homology k).map (FaceMapPairMap' n i))
  hom_inv_id := by simp
  inv_hom_id := by simp


-- def FaceMaoReducedInduceIso' (k : ℤ) : (H.homology k).obj P(Δ(n),∂Δ(n)) ≃ₗ[R] (H.homology k).obj P(@horn_sub_boundary (n+1) i) := CategoryTheory.Iso.toLinearEquiv (@FaceMaoReducedInduceIso R _ H n i k)

variable (n : ℕ) [NeZero n] (i : Fin (n+1))

-- Now we look at the triple `Δ(n), ∂Δ(n), Λ(n,i)`

-- this needs some checking

def SimplexHornMapToVertex : P(Δ(n), Λ(n,i)) ⟶ toPair₂ ({Ver n i} : Set Δ(n)) where
  toFun := fun _ ↦ ⟨Ver n i, rfl⟩
  continuous_toFun := by continuity -- exactly what?
  sub_map := fun _ ↦ ⟨Ver n i, rfl⟩
  comm := by ext; simp

def VertexMapToSimplexHorn : toPair₂ ({Ver n i} : Set Δ(n)) ⟶ P(Δ(n), Λ(n,i)) where
  toFun := fun x ↦ x.1
  continuous_toFun := by continuity
  sub_map := fun x ↦ ⟨x.1, by
    rw [x.2]
    exact vertex_in_horn
    ⟩
  comm := by ext; simp

lemma lm0 (x : Δ(n)): (SimplexHornMapToVertex n i).toFun x = ⟨Ver n i, rfl⟩ := rfl

lemma lm1 : ∀ x, (VertexMapToSimplexHorn n i).toFun x = x.1 := fun _ ↦ rfl

lemma lm (x : Δ(n)): (SimplexHornMapToVertex n i ≫ VertexMapToSimplexHorn n i).toFun x = Ver n i := by
  simp [lm0, lm1]

lemma lm' (x : Δ(n)): (SimplexHornMapToVertex n i ≫ VertexMapToSimplexHorn n i) x = Ver n i := by apply lm

lemma lm'' (x : Δ(n)): toContinuousMap (SimplexHornMapToVertex n i ≫ VertexMapToSimplexHorn n i) x = Ver n i := by apply lm

@[simp]
lemma id_toFun_eq_id' {P: TopPair}: ↑(toContinuousMap (PairMap.id P)) = id := by rfl

def test2 : PairMap.PairHomotopy (SimplexHornMapToVertex n i ≫ VertexMapToSimplexHorn n i) (𝟙 P(↑(SimplexCategory.toTopObj (SimplexCategory.mk n)), Λ(n, i))) where
  toFun f := by
    dsimp at f
    exact ⟨fun j : Fin (n+1) ↦ if j = i then ⟨(1 - f.1.1) * (1 - f.2 i) + f.2 i, by
      apply add_nonneg
      apply mul_nonneg
      simp only [sub_nonneg]
      exact f.1.2.2
      simp
      apply le_one
      exact (f.2 i).2
    ⟩ else ⟨f.1.1 * f.2 j, by
      apply mul_nonneg
      exact f.1.2.1
      exact (f.2 j).2⟩ , by sorry
        ⟩
  continuous_toFun := sorry
  map_zero_left := by
    intro x
    rw [lm'' n i x]
    simp
    ext j
    simp
    split_ifs with hj
    rw [hj]
    simp
    rfl
    rw [ver_app₂]
    rfl
    exact hj
  map_one_left := by
    intro x
    simp only [TopPairCategory.id_eq_pairmap_id]
    rw [id_toFun_eq_id']
    simp
    ext j
    simp
    split_ifs with hj
    rw [hj]
    rfl
    rfl
  prop' := sorry

def SimplexHornMapPairHomotopicToVertex : P(Δ(n), Λ(n,i)) ≃ₕ toPair₂ ({Ver n i} : Set Δ(n)) where
  toFun := SimplexHornMapToVertex n i
  invFun := VertexMapToSimplexHorn n i
  left_inv := ⟨test2 n i⟩
  right_inv := sorry

variable (k : ℤ)

def SimplexBoundaryHorn : TopTriple where
  total := Δ(n)
  isTotalTopologicalSpace := by infer_instance
  sub₁ := ∂Δ(n)
  sub₂ := Λ(n,i)
  inc := horn_sub_boundary


instance : IsIso (TripleBoundaryOp (SimplexBoundaryHorn n i) H k) := triple_pair_homotopic_points_of_boundary_isiso (SimplexBoundaryHorn n i) H (SimplexHornMapPairHomotopicToVertex n i)

def SimplexBoundaryIsoToBoundaryHorn : (H.homology (k+1)).obj P(Δ(n),∂Δ(n)) ≅ (H.homology k).obj Pᵢ(@horn_sub_boundary n i) := by
  have : k = k + 1 - 1 := by ring
  nth_rw 2 [this]
  exact asIso (TripleBoundaryOp (SimplexBoundaryHorn n i) H (k+1))

def SimplexBoundaryIsoSimplexBoundary : (H.homology k).obj P(Δ(n), ∂Δ(n)) ≅ (H.homology (k+1)).obj P(Δ(n+1),∂Δ(n+1)) := CategoryTheory.Iso.trans (FaceMaoReducedInduceIso n i k) (SimplexBoundaryIsoToBoundaryHorn (n+1) i k).symm

def SimplexBoundaryIsoSimplexBoundaryZero : (H.homology k).obj P(Δ(0), ∂Δ(0)) ≅ (H.homology (k+n)).obj P(Δ(n),∂Δ(n)) := by
  induction n
  case zero => simp; apply Iso.refl
  case succ n hn =>
    simp
    apply Iso.trans (hn 0)
    have : k + (n + 1) = k + n + 1 := by ring
    rw [this]
    exact @SimplexBoundaryIsoSimplexBoundary R _ H n 0 (k+n)


end TopologicalSimplex
end Homology_of_Topological_Simplex

-- TODO : Rename those face maps....
