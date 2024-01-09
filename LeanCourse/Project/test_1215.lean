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


universe u v w
-- variable {α β α' β' α'' β'': Type}isEmbedding
-- variable [TopologicalSpace α]  [TopologicalSpace β]

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

@[simp]
lemma to_pair_total_eq_self {α : Type} [TopologicalSpace α]: (toPair α).total = α := rfl

@[simp]
lemma to_pair_sub_eq_empty {α : Type} [TopologicalSpace α] : (toPair α).sub = Empty := rfl

@[simp]
lemma to_pair_map_empty_rec {α : Type} [TopologicalSpace α]: (toPair α).map = Empty.rec := rfl

def toPair₂ (α : Type) [TopologicalSpace α]: TopPair where
  total := α
  sub := α
  isTotalTopologicalSpace := by infer_instance
  isSubTopologicalSpace := by infer_instance
  map := id
  isEmbedding := embedding_id

@[simp]
lemma to_pair'_total_eq_self {α : Type} [TopologicalSpace α]: (toPair₂ α).total = α := rfl

@[simp]
lemma to_pair'_sub_eq_self {α : Type} [TopologicalSpace α] : (toPair₂ α).sub = α := rfl

@[simp]
lemma to_pair'_map_eq_id {α : Type} [TopologicalSpace α]: (toPair₂ α).map = id := rfl

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

def SubsettoPair₂ {α : Type} [TopologicalSpace α] {β γ: Set α} (h : γ ⊆ β): TopPair where
  total := β
  sub := γ
  isTotalTopologicalSpace := by infer_instance
  isSubTopologicalSpace := by infer_instance
  map := fun x ↦ ⟨x.1, h x.2⟩
  isEmbedding := by apply Embedding.codRestrict embedding_subtype_val

scoped[TopPair] notation "P("h")" => SubsettoPair₂ h

@[simp]
lemma subset_to_pair_total_eq_total' {α : Type} [TopologicalSpace α] {β γ: Set α} (h : γ ⊆ β): P(h).total = β := rfl

@[simp]
lemma subset_to_pair_sub_eq_sub' {α : Type} [TopologicalSpace α] {β γ: Set α} (h : γ ⊆ β): P(h).sub = γ := rfl

@[simp]
lemma subset_to_pair_map_eq_inc' {α : Type} [TopologicalSpace α] {β γ: Set α} (h : γ ⊆ β): P(h).map = fun x ↦ ⟨x.1, h x.2⟩ := rfl
end TopPair

@[ext]
structure PairMap (P₁ : TopPair) (P₂ : TopPair) extends C(P₁.total, P₂.total) where
  sub_map : P₁.sub → P₂.sub
  comm : toFun ∘ P₁.map = P₂.map ∘ sub_map

namespace PairMap
variable {P P₁ P₂ P₃ : TopPair}
open TopPair

-- this is no good
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

/-
class PairMapClass (F : Type) {α β α' β' : Type} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace α'] [TopologicalSpace β'] (P₁ : TopPair α β) (P₂ : TopPair α' β') extends ContinuousMapClass F α α'
-/

instance PairMapContinuousMapClass : ContinuousMapClass (PairMap P₁ P₂) P₁.total P₂.total where
  coe := fun f ↦ f.toFun
  coe_injective' := by
    intro f f' h
    ext1
    exact h
    exact sub_map_unique h
  map_continuous := fun f ↦ f.continuous

@[simp]
lemma coe_eq_toFun (f : PairMap P₁ P₂) : ↑f = f.toFun := by rfl

@[simp]
lemma toCont_toFun_eq_toFun (f : PairMap P₁ P₂) : f.toContinuousMap.toFun = f.toFun := by rfl

@[simp]
lemma toCont_toFun_eq_toFun' (f : PairMap P₁ P₂) : ContinuousMap.toFun f.toContinuousMap = f.toFun := by rfl


@[simp]
lemma comm_ele (f : PairMap P₁ P₂) : ∀ b, f (P₁.map b) = P₂.map (f.sub_map b) := by
  intro b
  calc f (P₁.map b) = (f ∘ P₁.map) b := rfl
  _ = (P₂.map ∘ f.sub_map) b := by simp only [coe_eq_toFun, f.comm]
  _ = P₂.map (f.sub_map b) := rfl

@[simp]
lemma image_sub (f : PairMap P₁ P₂) : ∀ b : P₁.sub, ∃ b' : P₂.sub, P₂.map b' = f (P₁.map b) := by
  intro b
  use f.sub_map b
  exact (comm_ele f b).symm

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

@[simp]
lemma comm' (f: PairMap P₁ P₂) : ↑f ∘ P₁.map = P₂.map ∘ f.sub_map := by simp only [coe_eq_toFun, f.comm]

open Set in
protected def comp (f : PairMap P₁ P₂) (g : PairMap P₂ P₃) : PairMap P₁ P₃ where
  toFun := g ∘ f
  continuous_toFun := by continuity
  sub_map := g.sub_map ∘ f.sub_map
  comm := by
    simp only [coe_comp_toFun]
    calc (↑g ∘ ↑f) ∘ P₁.map = ↑g ∘ (↑f ∘ P₁.map) := by rfl -- any lemma to rw??
      _ = ↑g ∘ (P₂.map ∘ f.sub_map) := by rw [f.comm']
      _ = (↑g ∘ P₂.map) ∘ f.sub_map := by rfl
      _ = (P₃.map ∘ g.sub_map) ∘ f.sub_map := by rw [g.comm']

infixr:200 " ◾ "  => PairMap.comp

@[ext]
lemma pairmap_eq_iff_toFun_eq {f g: PairMap P₁ P₂} (h : f.toFun = g.toFun) : f = g := by
  ext1
  exact h
  exact sub_map_unique h

@[simp]
lemma comp_toFun_eq_toFun_comp {f : PairMap P₁ P₂} {g : PairMap P₂ P₃}  : (PairMap.comp f g).toFun = g.toFun ∘ f.toFun := by rfl

@[simp]
lemma comp_submap_eq_sub_map_comp {f : PairMap P₁ P₂} {g : PairMap P₂ P₃}  : (PairMap.comp f g).sub_map = g.sub_map ∘ f.sub_map := by rfl


@[simp]
theorem comp_id (f: PairMap P₁ P₂) : PairMap.comp f (PairMap.id P₂) = f := by
  apply pairmap_eq_iff_toFun_eq
  /-
  -- why this???
  ⊢ (PairMap.comp f PairMap.id).toContinuousMap.toFun = f.toFun
  -/
  simp only [comp_toFun_eq_toFun_comp, id_toFun_eq_id]
  simp


@[simp]
theorem id_comp (f : PairMap P₁ P₂) : PairMap.comp (PairMap.id P₁) f = f := by
  apply pairmap_eq_iff_toFun_eq
  simp only [comp_toFun_eq_toFun_comp, id_toFun_eq_id]
  simp

@[simp]
theorem comp_assoc {P₄ : TopPair} (f : PairMap P₁ P₂) (g : PairMap P₂ P₃) (h : PairMap P₃ P₄) :
  PairMap.comp (PairMap.comp f g) h = PairMap.comp f (PairMap.comp g h) := by
  apply pairmap_eq_iff_toFun_eq
  simp only [comp_toFun_eq_toFun_comp]
  rfl


-- Define a pair map ` X = (X, ∅) → (X, A) `, whose role in the long exact sequence is comparable a projection, so I'll call it so

def PairTotalToPair (P : TopPair) : TopPair := toPair (P.total)

@[simp]
lemma to_pair_total_map_empty_rec {P : TopPair}: (PairTotalToPair P).map = Empty.rec := rfl

def ProjPairMap (P : TopPair) : PairMap (PairTotalToPair P) P where
  toFun := id
  continuous_toFun := by continuity
  sub_map := Empty.rec
  comm := by ext x; exact Empty.rec x

-- A pair map induces a map between the subspaces

-- If f : P ⟶ P' and P'.sub is empty then P must be empty

lemma target_sub_empty_of_source_sub_empty (f : PairMap P₁ P₂) (h : IsEmpty P₂.sub) : IsEmpty P₁.sub := by
  by_contra h'
  simp at h'
  obtain ⟨a, _⟩ := image_sub f (Classical.choice h')
  exact h.false a

-- Define the operation of excision

-- Subspace topology is already define
-- subtype not subset nor subspace
variable (U : Set P.sub)

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
  map := fun x ↦ (⟨P.map x, excision_is_in _ _⟩ : ((P.map '' U)ᶜ : Set P.total))
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
lemma excision_map_eq_self_map {P : TopPair} {U : Set P.sub} {x : (Uᶜ : Set P.sub)}: ((Excision P U).map x).1 = P.map x.1 := rfl

@[simp]
lemma excision_total_eq_total_excision {P : TopPair} {U : Set P.sub}: (Excision P U).total = ((P.map '' U)ᶜ : Set P.total) := rfl

@[simp]
lemma excision_sub_eq_sub_excision {P : TopPair} {U : Set P.sub}: (Excision P U).sub = (Uᶜ : Set P.sub) := rfl

def ExcisionInc (P : TopPair) (U : Set P.sub) : PairMap (Excision P U) P where
  toFun := fun x ↦ x.1
  continuous_toFun := by continuity
  sub_map := fun x ↦ x.1
  comm := by ext; simp

end PairMap
/-
  Category
-/
/-
variable {C : TopPair}
instance : CoeDep TopPair C (TopPair C.total C.sub) where
  coe := C
-/
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

@[simp]
lemma id_eq_pairmap_id {P : TopPair} : 𝟙 P = PairMap.id P := rfl

@[simp]
lemma comp_eq_pairmap_comp {P₁ P₂ P₃ : TopPair} {f : P₁ ⟶ P₂} {g : P₂ ⟶ P₃} : f ≫ g = PairMap.comp f g := rfl

@[ext]
lemma pairmap_eq_iff_toFun_eq' {f g: P₁ ⟶ P₂} (h : f.toFun = g.toFun) : f = g := PairMap.pairmap_eq_iff_toFun_eq h
end TopPairCategory

namespace PairMap
variable {P P₁ P₂ P₃ : TopPair}
open TopPair PairMap

def PairMapToSubPairMap (f : P₁ ⟶ P₂) : (toPair P₁.sub) ⟶ (toPair P₂.sub) where
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

end PairMap



section PairHomotopy
namespace PairMap
variable {P₁ P₂ : TopPair}
/-
  Homotopy of pairs
-/

open ContinuousMap PairMap
/-
structure PairHomotopy (f₀ f₁ : PairMap P P') extends Homotopy (f₀ : C(α, α')) f₁ where
  always_image_sub : ∀ t, RangeSub ((fun x ↦ toFun (t, x)) ∘ P.map) P'.map
-/

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

def toPairMap {α β : Type} [TopologicalSpace α] [TopologicalSpace β] (f : C(α, β)): (toPair α) ⟶ (toPair β) where
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

end PairMap
section PairHomotopy

/-
  Functor
-/

namespace Homology

/-
protected def trivial (R : Type*) [Ring R] : TopPair ⥤ ModuleCat R where
  obj := fun _ ↦
  map := _
  map_id := _
  map_comp := _
-/
variable {R : Type*} [Ring R]
variable {P : TopPair} {P' : TopPair}
open PairMap TopPair
open Function

section Homotopy_invariance
structure HomotopyInvariant (F : TopPair ⥤ ModuleCat R) : Prop :=
  homotopy_inv {P P' : TopPair} {f f' : P ⟶ P'}: f ≃ₕ f' → (F.map f = F.map f')

variable {F : TopPair ⥤ ModuleCat R} (h :HomotopyInvariant F)
-- Send homotopy equivalence to isomorphism

lemma homotopy_inv_id_to_id {f : P ⟶ P} (htp : f ≃ₕ (𝟙 P)) : F.map f = 𝟙 (F.obj P) := by
  rw [← F.map_id]
  apply h.homotopy_inv
  exact htp


instance homotopy_inv_equi_of_iso {f : P ⟶ P'} [htp : IsPairHomotopyEquiv f] : IsIso (F.map f) where
  out := by
    use F.map (inv f)
    repeat rw [← F.map_comp, TopPairCategory.comp_eq_pairmap_comp]
    exact ⟨homotopy_inv_id_to_id h <| hom_inv_id f, homotopy_inv_id_to_id h <| inv_hom_id f⟩

end Homotopy_invariance

/-
  Excisive
-/

structure Excisive {R : Type*} [Ring R] (F : TopPair ⥤ ModuleCat R) : Prop :=
  excisive : ∀ P, ∀ U : Set (P.sub), IsIso (F.map (ExcisionInc P U))


-- this is bad consider usig type class
lemma excisive_iff_induce_iso {R : Type*} [Ring R] (F : TopPair ⥤ ModuleCat R) (h : Excisive F) {P : TopPair} {U : Set (P.sub)} : IsIso (F.map (ExcisionInc P U)) := h.excisive P U

/-
  additivity
-/

#check @Sigma.mk
#check instTopologicalSpaceSigma


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


structure Additive {R : Type*} [Ring R] (F : TopPair ⥤ ModuleCat R) : Prop :=
  additivity {ι : Type} (P : ι → TopPair) (i : ι): IsIso (F.map (SigmaTopPairInc P i))

-- the long exact sequence consisting of three parts

/-
instance (R: Type) [Ring R] : Coe (HomotopyInvExcisionFunctor R) (Functor TopPair (ModuleCat R)) where
  coe := HomotopyInvExcisionFunctor.toFunctor
-/


def ProjPairMap' (P : TopPair) : (toPair P.total) ⟶ P := ProjPairMap P

def IncPairMap' (P : TopPair) : (toPair P.sub) ⟶ (toPair P.total) where
  toFun := P.map
  continuous_toFun := Embedding.continuous P.isEmbedding
  sub_map := Empty.rec
  comm := by simp

@[simp]
lemma inc_pair_map'_to_fun_eq_pair_emb {P : TopPair}: (IncPairMap' P).toFun = P.map := rfl

@[simp]
lemma inc_pair_map'_self_to_fun_eq_id {α : Type} [TopologicalSpace α]: (IncPairMap' (toPair₂ α)).toFun = id := rfl

variable {F G : TopPair ⥤ ModuleCat R}

structure InjProjExact (F : TopPair ⥤ ModuleCat R) (P : TopPair) : Prop where
  inj_proj_exact : Function.Exact (F.map (IncPairMap' P)) (F.map (ProjPairMap' P))

-- an endofunctor of TopPair ` (α , β) ↦ (β, ∅)

-- def PairToSubFunctor.{u₁, u₂} : TopPair.{u₁, u₂} ⥤ TopPair.{u₂, 0} where
def PairToSubFunctor : TopPair ⥤ TopPair where
  obj P := toPair P.sub
  map := PairMapToSubPairMap
  map_id := @id_to_sub_pair_map_eq_id
  map_comp := @to_sub_pair_map_comp

#check ModuleCat R
-- example (α β: Type) (h : IsEmpty α) : α → β := h.elim

-- abbrev BoundaryOp.{u₁, u₂, u₃, u₄} {R : Type* u₁} [Ring R] (F : TopPair.{u₂, u₃} ⥤ ModuleCat.{u₄} R) (G : TopPair.{u₃, 0} ⥤ ModuleCat.{u₄} R) := NatTrans F (PairToSubFunctor ⋙ G)

abbrev BoundaryOp (F : TopPair ⥤ ModuleCat R) (G : TopPair ⥤ ModuleCat R) := NatTrans F (PairToSubFunctor ⋙ G)


#check BoundaryOp

structure ProjBoundExact {F G : TopPair ⥤ ModuleCat R} (bd :BoundaryOp F G) (P : TopPair) : Prop where
  proj_bound_exact : Function.Exact (F.map (ProjPairMap' P)) (bd.app P)

structure BoundInjExact {F G : TopPair ⥤ ModuleCat R} (bd :BoundaryOp F G) (P : TopPair) : Prop where
  bound_inj_exact : Function.Exact (bd.app P) (G.map (IncPairMap' P))

/-
define a coecion from HomotopyInvExcisionFunctor to Functor
-/
/-
instance (α : Type) [Unique α]: TopologicalSpace α := TopologicalSpace.generateFrom ⊤
-/
structure ExOrdHomology (R : Type*) [Ring R] where
  homology (n : ℤ): TopPair ⥤ ModuleCat R
  homotopy_inv : ∀ n,  HomotopyInvariant (homology n)
  excisive : ∀ n, Excisive (homology n)
  additive : ∀ n, Additive (homology n)
  boundary_op (n : ℤ) : BoundaryOp (homology n) (homology (n-1))
  exact_seq_inj_proj : ∀ n, ∀ P, InjProjExact (homology n) P
  exact_seq_proj_bound : ∀ n, ∀ P, ProjBoundExact (boundary_op n) P
  exact_seq_bound_inj : ∀ n, ∀ P, BoundInjExact (boundary_op n) P


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
def EmbeddingInduceIso (P : TopPair) (H : ExOrdHomology R) : Prop := ∀ k, IsIso ((H.homology k).map (IncPairMap' P))

lemma inclusion_induce_iso_of_homology_trivial {P : TopPair} (h : EmbeddingInduceIso P H) : ∀ k, Subsingleton ((H.homology k).obj P) :=
  fun k ↦ exact_iso_iso_of_subsingleton (H.exact_seq_inj_proj k P).inj_proj_exact (H.exact_seq_proj_bound k P).proj_bound_exact (H.exact_seq_bound_inj k P).bound_inj_exact (h k) (h <| k - 1)

instance toPair₂_inc_pair_map_iso {α : Type} [TopologicalSpace α] : IsIso (IncPairMap' (toPair₂ α)) := by
  use IncPairMap' (toPair₂ α)
  constructor
  . ext1
    simp only [comp_eq_pairmap_comp, comp_toFun_eq_toFun_comp, inc_pair_map'_self_to_fun_eq_id, to_pair'_sub_eq_self, to_pair'_total_eq_self, Function.comp.right_id, id_eq_pairmap_id, id_toFun_eq_id]
  . ext1
    simp only [to_pair'_total_eq_self, to_pair'_sub_eq_self, comp_eq_pairmap_comp, comp_toFun_eq_toFun_comp, id_eq_pairmap_id, inc_pair_map'_self_to_fun_eq_id, Function.comp.right_id, id_toFun_eq_id]

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
  have : IncPairMap' P ≫ f₁ = f₂ ≫ (IncPairMap' <| toPair₂ α) := by
    ext1
    simp only [to_pair_total_eq_self, to_pair'_total_eq_self, comp_eq_pairmap_comp, comp_toFun_eq_toFun_comp, inc_pair_map'_to_fun_eq_pair_emb, to_pair'_sub_eq_self]
    repeat rw [to_pair_map_to_fun_eq_self']
    simp only [to_pair'_map_eq_id, to_pair'_sub_eq_self]
    ext x
    have : Subsingleton (toPair₂ α).total := by simp; infer_instance
    apply (eq_iff_true_of_subsingleton ((f.toFun ∘ P.map) x) ((id ∘ f.sub_map) x)).mpr trivial
  have aux := congrArg (H.homology k).map this
  repeat rw [(H.homology k).map_comp] at aux
  have : IsIso ((ExOrdHomology.homology H k).map f₁) := homotopy_inv_equi_of_iso <| H.homotopy_inv k
  have : IsIso ((ExOrdHomology.homology H k).map f₂) := homotopy_inv_equi_of_iso <| H.homotopy_inv k
  have : IsIso <| (ExOrdHomology.homology H k).map (IncPairMap' P) ≫ (ExOrdHomology.homology H k).map f₁ := by
    rw [aux]
    apply IsIso.comp_isIso
  -- better make homotopy_inv a class
  apply IsIso.of_isIso_comp_right ((ExOrdHomology.homology H k).map (IncPairMap' P)) ((ExOrdHomology.homology H k).map f₁)


lemma pair_homotopic_points_of_homology_trivial (H : ExOrdHomology R) {P : TopPair} {α : Type} [TopologicalSpace α] [Unique α] (htp : P ≃ₕ toPair₂ α) : ∀ k, Subsingleton ((H.homology k).obj P) :=
  inclusion_induce_iso_of_homology_trivial <| pair_homotopic_points_of_inc_induce_iso htp.toFun


/--
  If `A` of `(X, A)` has zero homology at `k` and `k-1`, then the projection induces an isomorphism `h_k(X) → h_k(X,A)`
-/
lemma pair_zero_homology_of_proj_induce_iso {P : TopPair} (k : ℤ) (h₁ : Subsingleton <| (H.homology k).obj <| toPair P.sub) (h₂ : Subsingleton <| (H.homology (k-1)).obj <| toPair P.sub) : IsIso <| (H.homology k).map <| ProjPairMap' P:= exact_subsingleton_subsingleton_of_isiso (H.exact_seq_inj_proj k P).inj_proj_exact (H.exact_seq_proj_bound k P).proj_bound_exact h₁ h₂


/--
  If `X` of `(X, A)` has zero homology at `k` and `k-1`, then the boundary operator `h_k(X,A) → H_{k-1}(A)` is an isomorphism
-/
lemma pair_zero_homology_of_boundary_op_iso {P : TopPair} (k : ℤ) (h₁ : Subsingleton <| (H.homology k).obj <| toPair P.total) (h₂ : Subsingleton <| (H.homology (k-1)).obj <| toPair P.total) : IsIso <| (H.boundary_op k).app P := exact_subsingleton_subsingleton_of_isiso (H.exact_seq_proj_bound k P).proj_bound_exact (H.exact_seq_bound_inj k P).bound_inj_exact h₁ h₂

end Extraordinary

end Homology
end Basic_results_of_homology

section Long_exact_sequence_of_triple
namespace Homology
open TopPair PairMap Homology
-- I don't wanna define a topological triple
-- I will temporarily work with `X ⊃ A ⊃ B`
variable (α: Type) [TopologicalSpace α]
variable (β γ: Set α) (h: γ ⊆ β)

def TripleInc₁ : P(h) ⟶ P(α, γ) where
  toFun x := x.1
  continuous_toFun := by continuity
  sub_map := id
  comm := by ext; simp

def TripleInc₂ : P(α, γ) ⟶ P(α, β) where
  toFun := id
  continuous_toFun := by continuity
  sub_map x := ⟨x.1, h x.2⟩
  comm := by ext; simp

variable {R : Type*} [Ring R] (H : ExOrdHomology R) (k : ℤ)

def TripleBoundaryOp : (H.homology k).obj P(α, β) ⟶ (H.homology <| k-1).obj P(h) := ((H.boundary_op k).app P(α, β)) ≫ ((H.homology (k-1)).map <| ProjPairMap' P(h))

lemma triple_exact_inc₁_inc₂ {α: Type} [TopologicalSpace α] {β γ: Set α} {h: γ ⊆ β} : Function.Exact ((H.homology k).map <| TripleInc₁ α β γ h)  ((H.homology k).map <| TripleInc₂ α β γ h) := sorry

lemma triple_exact_inc₂_boundary {α: Type} [TopologicalSpace α] {β γ: Set α} {h: γ ⊆ β} : Function.Exact ((H.homology k).map <| TripleInc₂ α β γ h) (TripleBoundaryOp α β γ h H k) := sorry

lemma triple_exact__boundary_inc₁ {α: Type} [TopologicalSpace α] {β γ: Set α} {h: γ ⊆ β} : Function.Exact (TripleBoundaryOp α β γ h H k) ((H.homology <| k-1).map <| TripleInc₁ α β γ h):= sorry

/--
  For a triple `(α, β, γ)`, if `(α, γ)` is homotopic to `(*, *)`, then `h_{k+1}(α, β) → h_k(β, γ)` is an isomorphism everywhere
-/
lemma triple_pair_homotopic_points_of_boundary_isiso {σ : Type} [TopologicalSpace σ] [Unique σ] (htp : P(α, γ) ≃ₕ toPair₂ σ) (k : ℤ) : IsIso (TripleBoundaryOp α β γ h H k) := by
  have h₁ := pair_homotopic_points_of_homology_trivial H htp k
  have h₂ := pair_homotopic_points_of_homology_trivial H htp (k-1)
  have e₁ := @triple_exact_inc₂_boundary R _ H k α _ β γ h
  have e₂ := @triple_exact__boundary_inc₁ R _ H k α _ β γ h
  apply exact_subsingleton_subsingleton_of_isiso e₁ e₂ h₁ h₂

end Homology
end Long_exact_sequence_of_triple

namespace TopologicalSimplex
#check SimplexCategory.toTopMap
open SimplexCategory
open Simplicial BigOperators

#check (toTopObj ([0]))
#check (CategoryTheory.forget SimplexCategory).obj ([0])


-- to distinguish from Δ[n], which is a simplicial set
notation  "Δ("n")" => toTopObj [n]

/-
@[simp]
lemma test' : (CategoryTheory.forget SimplexCategory).obj ([0]) = Fin 1 := rfl

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
-/
open TopPair Homology
/-
variable {R : Type*} [Ring R] (H : OrdHomology R)

#check Nontrivial

example (n: ℤ): Nontrivial ((H.homology n).obj (toPair (Δ(0)))) → n = 0:= H.dimension n (Δ[0])
-/

-- need to define boundary of simplex (SSet.boundary is a SSet, too complicated to work with)

open Set
@[ext]
structure DownwardClosed (n : ℕ) where
  carrier : Set (Set (Fin (n + 1)))
  downward_closed : ∀ I J, J ∈ carrier ∧ I.Nonempty ∧ I ⊆ J → I ∈ carrier

instance (n : ℕ) : SetLike (DownwardClosed n)  (Set (Fin (n + 1))) where
  coe s := s.carrier
  coe_injective' := by intro _ _ h; ext1; exact h

example (α : Type) (x y : Set α) : x = univ → x ⊆ y → y = univ := by
  intro h h'
  apply univ_subset_iff.mp
  rwa [h] at h'


-- Col for collection
def BoundaryCol (n : ℕ) : DownwardClosed n where
  carrier := {I | I.Nonempty ∧ I ≠ univ}
  downward_closed := by
    intro I J h
    constructor
    . exact h.2.1
    . by_contra h'
      rw [h'] at h
      have : J = univ := univ_subset_iff.mp h.2.2
      exact h.1.2 this

#check Fin.succAboveEmb
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
      . apply h1.2.1
        apply univ_subset_iff.mp
        intro j _
        by_cases hj : j ≠ i
        exact h3 hj
        simp at hj
        rwa [← hj] at hi
      . apply h1.2.2
        apply subset_antisymm ?_ h3
        intro j hj
        simp
        intro h
        apply hi
        rwa [h] at hj




def Realization {n : ℕ} (U : DownwardClosed n) :=
  {f : Δ(n)| { i : Fin (n + 1) | f i ≠ 0 } ∈ U.carrier}


-- this is solved, but there should be a more basic tactic
lemma mem_realization_iff {n : ℕ} {U : DownwardClosed n} {f : Δ(n)} : f ∈ Realization U ↔ { i : Fin (n + 1) | f i ≠ 0 } ∈ U.carrier := by simp [Realization]

notation "∂Δ("n")" => Realization (BoundaryCol n)

notation "Λ("n", "i")" => Realization (HornCol n i)

-- #check Λ(n,i)

-- #check P(Δ(n), ∂Δ(n))

-- face maps are already defined

notation "d("n", "i")" => toTopMap (@δ n i)

-- face maps restrict to bouandary, and boundary restricts to horn

lemma realization_mono {n : ℕ} {U₁ U₂: DownwardClosed n} (h: U₁.1 ⊆ U₂.1): Realization U₁ ⊆ Realization U₂ := by
  simp only [Realization]
  intro _ hf
  exact h hf

lemma sum_eq_one {n : ℕ} (f : Δ(n)) : ∑ i, f i = 1 := by
  simp [toTopObj] at f
  exact f.2


lemma exsit_nonzero {n : ℕ} (f : Δ(n)) : ∃ j, f j ≠ 0 := by
  by_contra h
  simp at h
  have : ∑ i, f i = 0 := by
    apply Finset.sum_eq_zero
    simp [h]
  rw [sum_eq_one f] at this
  norm_num at this


#check Finset.univ

lemma horn_sub_boundary {n : ℕ} {i : Fin (n + 1)} : Λ(n, i) ⊆ ∂Δ(n) := by
  apply realization_mono
  have h1 : (HornCol n i).carrier = {I | I.Nonempty ∧ I ≠ univ ∧ I ≠ {j | j ≠ i }} := rfl
  have h2 : (BoundaryCol n).carrier = {I | I.Nonempty ∧ I ≠ univ} := rfl
  simp [h1, h2]
  intro a h h' _
  exact ⟨h, h'⟩

def Horn' {n : ℕ} {i : Fin (n + 1)} : Set ∂Δ(n) := {(⟨x.1, horn_sub_boundary x.2⟩ : ∂Δ(n)) | x : Λ(n,i)}

notation "Λ'("n", "i")" => @Horn' n i

open Classical -- solve decidability ......

lemma face_map_miss_one_vertex {n: ℕ} {i: Fin (n + 2)} {x : Δ(n)} : (d(n,i) x) i = 0 := by
  simp
  intro k hk
  exfalso
  apply Fin.succAbove_ne i k hk

lemma face_map_exist_nonzero {n: ℕ} {i: Fin (n + 2)} {x : Δ(n)} : Set.Nonempty {j | (d(n,i) x) j ≠ 0} := by
  obtain ⟨j, hj⟩ := exsit_nonzero x
  use (δ i) j -- ` : Fin (n + 2) `
  simp
  use j

lemma face_map_exist_zero {n: ℕ} {i: Fin (n + 2)} {x : Δ(n)} : {j | (d(n,i) x) j ≠ 0} ≠ univ := by
  by_contra h
  have : i ∈ {j | (toTopMap (δ i) x) j ≠ 0} := by
    rw [h]; simp
  simp at this
  obtain ⟨j, hj, _⟩ := this
  apply (Fin.succAbove_ne i j) hj

lemma face_map_image_sub_boundary {n : ℕ} {i : Fin (n + 2)} {x : Δ(n)} : d(n,i) x ∈ ∂Δ(n+1) := by
  apply mem_realization_iff.mpr
  have : (BoundaryCol (n+1)).carrier = {I | I.Nonempty ∧ I ≠ univ} := rfl
  simp only [this]
  exact ⟨face_map_exist_nonzero, face_map_exist_zero⟩

lemma face_map_image_of_boundary_sub_horn {n : ℕ} {i : Fin (n + 2)} {x : ∂Δ(n)} : d(n,i) x ∈ Λ(n+1, i) := by
  apply mem_realization_iff.mpr
  have : (HornCol (n+1) i).carrier = {I | I.Nonempty ∧ I ≠ univ ∧ I ≠ {j | j ≠ i }} := rfl
  simp only [this]
  clear this
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

-- decompose `d(n,i)` on `(Δ(n), ∂Δ(n))` into a deformation retract and an excision
--

/--
  vertex of simplexes
-/

def Ver (n : ℕ) (i : Fin (n + 1)) : Δ(n) where
  val k := if k = i then 1 else 0
  property := by simp [toTopObj]

lemma vertex_in_boundary {n : ℕ} [NeZero n] {i : Fin (n + 1)} : Ver n i ∈ ∂Δ(n) := by
  simp [mem_realization_iff, BoundaryCol]
  constructor
  . use i
    simp [Ver]
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

open PairMap

def BoundaryHornExciseVertex (n : ℕ) [NeZero n] (i : Fin (n+1)) := ExcisionInc P(horn_sub_boundary) {VerH n i}

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


def FaceMapReduced (n : ℕ) (i : Fin (n+2)): P(Δ(n), ∂Δ(n)) ⟶ (Excision P(horn_sub_boundary) {VerH (n+1) i}) where
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

def FaceMapPairMap' (n : ℕ) (i : Fin (n+2)): P(Δ(n), ∂Δ(n)) ⟶ P(@horn_sub_boundary (n+1) i) where
  toFun := fun x ↦ ⟨d(n,i) x, face_map_image_sub_boundary⟩
  continuous_toFun := by continuity
  sub_map := fun x ↦ ⟨d(n,i) x.1, face_map_image_of_boundary_sub_horn⟩
  comm := by ext; simp

lemma face_map_decompose_through_reduced_map : FaceMapPairMap' n i = (FaceMapReduced n i) ≫ (BoundaryHornExciseVertex (n+1) i) := by
  simp
  ext
  simp [FaceMapPairMap', FaceMapReduced, BoundaryHornExciseVertex, ExcisionInc]

-- lemma face_map_decompose_through_reduced_map' : (FaceMapPairMap n i : P(Δ(n), ∂Δ(n)) ⟶ P(Δ(n+1), ∂Δ(n+1))) = (FaceMapReduced n i : P(Δ(n), ∂Δ(n)) ⟶ (Excision P(Δ(n+1), ∂Δ(n+1)) {VerB (n+1) i})) ≫ (BoundaryHornExciseVertex (n+1) i) := by simp;

def FaceMapReducedPairHomotopyEquiv: P(Δ(n), ∂Δ(n)) ≃ₕ (Excision P(horn_sub_boundary) {VerH (n+1) i}) where
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
variable {H : OrdHomology R}
variable {n : ℕ} {i : Fin (n+2)}

-- maybe instance?
instance reduced_face_map_induce_iso {k : ℤ}: IsIso ((H.homology k).map (FaceMapReduced n i)) := homotopy_inv_equi_of_iso (H.homotopy_inv k)

instance excision_inc_induce_is_isp {k : ℤ} : IsIso ((H.homology k).map (BoundaryHornExciseVertex (n+1) i)) := by
  apply excisive_iff_induce_iso _ (H.excisive k)

instance face_map_induce_is_iso (k : ℤ) : IsIso ((H.homology k).map (FaceMapPairMap' n i)) := by
  rw [face_map_decompose_through_reduced_map, (H.homology k).map_comp]
  apply IsIso.comp_isIso

-- lemma subsingleton_unique_topology {α : Type} (h : Subsingleton α) [t1 : TopologicalSpace α] [t2 : TopologicalSpace α] : t1 = t2 := by simp only [eq_iff_true_of_subsingleton]

def FaceMaoReducedInduceIso (n : ℕ) (i : Fin (n + 1)) (k : ℤ) :(H.homology k).obj P(Δ(n),∂Δ(n)) ≅ (H.homology k).obj P(@horn_sub_boundary (n+1) i) where
  hom := (H.homology k).map (FaceMapPairMap' n i)
  inv := CategoryTheory.inv ((H.homology k).map (FaceMapPairMap' n i))
  hom_inv_id := by simp
  inv_hom_id := by simp


-- def FaceMaoReducedInduceIso' (k : ℤ) : (H.homology k).obj P(Δ(n),∂Δ(n)) ≃ₗ[R] (H.homology k).obj P(@horn_sub_boundary (n+1) i) := CategoryTheory.Iso.toLinearEquiv (@FaceMaoReducedInduceIso R _ H n i k)

variable (n : ℕ) [NeZero n] (i : Fin (n+1))
/-

-- This is wrong

def BoundaryHornMapToBoundaryPoint : P(∂Δ(n), {VerB n i}) ⟶ P(@horn_sub_boundary n i) where
  toFun := id
  continuous_toFun := by continuity
  sub_map := fun _ ↦ ⟨VerB n i, vertex_in_horn⟩
  comm := by
    ext x; simp; ext1; simp at x; simp
    have : x.1 = VerB n i := x.2
    simp [this]

def BoundaryHornMapBoundaryPointPairHomotopyEquiv : P(∂Δ(n), {VerB n i}) ≃ₕ P(@horn_sub_boundary n i) where
  toFun := BoundaryHornMapToBoundaryPoint n i
  invFun := sorry
  left_inv := sorry
  right_inv := sorry
-/

-- Now we look at the triple `Δ(n), ∂Δ(n), Λ(n,i)`

-- this needs some checking
#check ({Ver n i} : Set Δ(n))



def SimplexHornMapToVertex : P(Δ(n), Λ(n,i)) ⟶ toPair₂ ({Ver n i} : Set Δ(n)) where
  toFun := fun _ ↦ ⟨Ver n i, rfl⟩
  continuous_toFun := by continuity -- exactly what?
  sub_map := fun _ ↦ ⟨Ver n i, rfl⟩
  comm := by ext; simp

def SimplexHornMapPairHomotopicToVertex : P(Δ(n), Λ(n,i)) ≃ₕ toPair₂ ({Ver n i} : Set Δ(n)) where
  toFun := SimplexHornMapToVertex n i
  invFun := sorry
  left_inv := sorry
  right_inv := sorry

variable (k : ℤ)

#check TripleBoundaryOp Δ(n) ∂Δ(n) Λ(n,i) (@horn_sub_boundary n i) H.toExOrdHomology k

instance : IsIso (TripleBoundaryOp Δ(n) ∂Δ(n) Λ(n,i) (@horn_sub_boundary n i) H.toExOrdHomology k) := triple_pair_homotopic_points_of_boundary_isiso Δ(n) ∂Δ(n) Λ(n,i) (@horn_sub_boundary n i) H.toExOrdHomology (SimplexHornMapPairHomotopicToVertex n i) k

def SimplexBoundaryIsoToBoundaryHorn : (H.homology (k+1)).obj P(Δ(n),∂Δ(n)) ≅ (H.homology k).obj P(@horn_sub_boundary n i) := by
  have : k = k + 1 - 1 := by ring
  nth_rw 2 [this]
  exact asIso (TripleBoundaryOp Δ(n) ∂Δ(n) Λ(n,i) (@horn_sub_boundary n i) H.toExOrdHomology (k+1))

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
