-- change the def of TopPair to a direct bundle of things

import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.Homotopy.Equiv
import Mathlib.CategoryTheory.ConcreteCategory.BundledHom
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.Exact
noncomputable section

#check TopologicalSpace

universe u v w
-- variable {α β α' β' α'' β'': Type*}
-- variable [TopologicalSpace α]  [TopologicalSpace β]

@[ext]
class TopPair where
  total : Type*
  sub : Type*
  isTotalTopologicalSpace : TopologicalSpace total
  isSubTopologicalSpace : TopologicalSpace sub
  map : sub  → total
  isEmbedding : Embedding map

attribute [instance] TopPair.isTotalTopologicalSpace TopPair.isSubTopologicalSpace

/-- ` toPair ` sends a topological space ` α ` to a topological pair ` (α, ∅) `
-/
def toPair (α : Type*) [TopologicalSpace α]: TopPair where
  total := α
  sub := Empty
  isTotalTopologicalSpace := by infer_instance
  isSubTopologicalSpace := by infer_instance
  map := Empty.rec
  isEmbedding := by simp [embedding_iff, inducing_iff, Function.Injective]

@[simp]
lemma toPairSubEmpty {α : Type*} [TopologicalSpace α]: (toPair α).sub = Empty := rfl

def PairRangeSub (P₁ : TopPair) (P₂ : TopPair) (f : C(P₁.total, P₂.total)) : Prop :=
  Set.range (f ∘ P₁.map) ⊆ Set.range P₂.map

@[ext]
class PairMap (P₁ : TopPair) (P₂ : TopPair) extends C(P₁.total, P₂.total) where
  image_sub : PairRangeSub P₁ P₂ (ContinuousMap.mk toFun)


/-
class PairMapClass (F : Type*) {α β α' β' : Type*} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace α'] [TopologicalSpace β'] (P₁ : TopPair α β) (P₂ : TopPair α' β') extends ContinuousMapClass F α α'
-/

namespace PairMap
variable {P P' P'' : TopPair}

instance : ContinuousMapClass (PairMap P P') P.total P'.total where
  coe := fun f ↦ f.toFun
  coe_injective' := by
    intro f f' h
    ext1
    exact h
  map_continuous := fun f ↦ f.continuous

lemma PairMapImageSub {P₁ : TopPair} {P₂ : TopPair} (f : PairMap P₁ P₂) : ∀ b : P₁.sub, ∃ b' : P₂.sub, P₂.map b' = f (P₁.map b) := by
  have : PairRangeSub P₁ P₂ f := f.image_sub
  simp [PairRangeSub, Set.range] at this
  exact this

protected def id : PairMap P P where
  toFun := id
  -- continuous_toFun := continuous_id
  -- I don't need this field why?
  image_sub := by intro a ha; obtain ⟨b, hb⟩ := ha; use b; exact hb

open Set in
protected def comp (f : PairMap P' P'') (g : PairMap P P') : PairMap P P'' where
  toFun := f ∘ g
  image_sub := by
    simp
    calc range ((↑f ∘ ↑g) ∘ P.map) = range (↑f ∘ (↑g ∘ P.map)) := rfl
    _ ⊆ range (↑f ∘ P'.map) := by
      rw [range_comp, range_comp f]
      apply Set.image_subset
      exact g.image_sub
    _ ⊆ range (P''.map) := f.image_sub

#check Set.range
#check PairMap.comp

@[simp]
theorem comp_id (f : PairMap P P') : PairMap.comp f PairMap.id = f := by ext; simp

@[simp]
theorem id_comp (f : PairMap P P') : PairMap.comp PairMap.id f = f := by ext; simp

@[simp]
theorem comp_assoc {P''' : TopPair} (f'' : PairMap P'' P''') (f' : PairMap P' P'') (f : PairMap P P') :
  PairMap.comp (PairMap.comp f'' f') f = PairMap.comp f'' (PairMap.comp f' f) := by ext; simp

-- toPair induces a PairMap

def toPairMap {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] (f : C(α, β)): PairMap (toPair α) (toPair β) where
  toFun := f
  continuous_toFun := by continuity
  image_sub := by simp [PairRangeSub, Set.range]


-- Define a pair map ` X = (X, ∅) → (X, A) `, whose role in the long exact sequence is comparable a projection, so I'll call it so

def PairTotalToPair (P : TopPair) : TopPair := toPair (P.total)


def ProjPairMap (P : TopPair) : PairMap (PairTotalToPair P) P where
  toFun := id
  continuous_toFun := by continuity
  image_sub := by simp [PairRangeSub, Set.range];

-- A pair map induced a map between the subspaces

-- If f : P ⟶ P' and P'.sub is empty then P must be empty

lemma target_sub_empty_of_source_sub_empty (f : PairMap P P') (h : IsEmpty P'.sub) : IsEmpty P.sub := by
  by_contra h'
  simp at h'
  -- Classical.choose h'
  obtain ⟨a, _⟩ := PairMapImageSub f (Classical.choice h')
  exact h.false a

#check IsEmpty
#check if_pos

def PairMapToSubMap [Nonempty P'.sub] (f : PairMap P P') : C(P.sub, P'.sub) where
  toFun := Function.invFun (P'.map) ∘ f ∘ P.map
  continuous_toFun := by
    apply (Embedding.continuous_iff P'.isEmbedding).mpr
    have : P'.map ∘ Function.invFun (P'.map) ∘ f ∘ P.map = f ∘ P.map := by
      ext b
      obtain ⟨y, hy⟩ := PairMapImageSub f b
      simp [← hy]
      exact Function.apply_invFun_apply
    rw [this]
    apply Continuous.comp (by continuity) (Embedding.continuous P.isEmbedding)

def PairMapToSubPairMap [Nonempty P'.sub] (f : PairMap P P') : PairMap (toPair P.sub) (toPair P'.sub) := toPairMap (PairMapToSubMap f)

-- Empty case

def PairMapToSubMap' [IsEmpty P'.sub] (f : PairMap P P') : C(P.sub, P'.sub) where
  toFun := by
    have := target_sub_empty_of_source_sub_empty f (by infer_instance)
    exact this.elim
  continuous_toFun := by
    simp [continuous_iff_continuousAt]
    have := target_sub_empty_of_source_sub_empty f (by infer_instance)
    exact this.elim

def PairMapToSubPairMap' [IsEmpty P'.sub] (f : PairMap P P') : PairMap (toPair P.sub) (toPair P'.sub) := toPairMap (PairMapToSubMap' f)



-- Define the operation of excision

-- Subspace topology is already define
-- subtype not subset nor subspace
#check instTopologicalSpaceSubtype
variable (U : Set P.sub)

#check Set.inclusion

/-
failed to synthesize instance
  HasCompl (Type u_1)

def Excision : TopPair (P.map '' U)ᶜ  Uᶜ := by sorry
-/

lemma excision_is_in (x : (Uᶜ : Set P.sub)) : P.map (x : P.sub)  ∈ (P.map '' U)ᶜ := by
  intro h
  obtain ⟨x', hx'1, hx'2⟩ := h
  apply @(P.isEmbedding.inj) at hx'2
  have : (x : P.sub) ∈ Uᶜ := x.2 --- omg!!!
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
    . sorry
    . intro _ _ _ _ hab
      apply P.isEmbedding.inj hab

-- restriction is inducing...

def ExcisionInc (P : TopPair) (U : Set P.sub) : PairMap (Excision P U) P where
  toFun := fun x ↦ x.1
  continuous_toFun := by continuity
  image_sub := by
    simp [PairRangeSub, Set.range]
    intro x
    exact ⟨x.1, rfl⟩

/-
  Homotopy of pairs
-/

open ContinuousMap
/-
structure PairHomotopy (f₀ f₁ : PairMap P P') extends Homotopy (f₀ : C(α, α')) f₁ where
  always_image_sub : ∀ t, RangeSub ((fun x ↦ toFun (t, x)) ∘ P.map) P'.map
-/

structure PairHomotopy (f₀ f₁ : PairMap P P') extends HomotopyWith (f₀ : C(P.total, P'.total)) f₁ (PairRangeSub P P')

def PairHomotopic (f₀ f₁ : PairMap P P') : Prop :=
  Nonempty (PairHomotopy f₀ f₁)

@[ext]
structure PairHomotopyEquiv (P : TopPair) (P' : TopPair) where
  toFun : PairMap P P'
  invFun : PairMap P' P
  left_inv : PairHomotopy (invFun.comp toFun) PairMap.id
  right_inv : PairHomotopy (invFun.comp toFun) PairMap.id

infixl:25 " ≃ₕ " => PairMap.PairHomotopyEquiv

#check P ≃ₕ P'




-- coercion to HomotopyWith
end PairMap



/-
  Category
-/
/-
variable {C : TopPair}
instance : CoeDep TopPair C (TopPair C.total C.sub) where
  coe := C
-/

open CategoryTheory

instance TopPairegory : Category TopPair where
  Hom P Q := PairMap P Q
  id _ := PairMap.id
  comp f g := PairMap.comp g f
  id_comp _ := by simp
  comp_id _ := by simp
  assoc _ _ _ := by simp

/-
  Functor
-/

variable {R : Type*} [Ring R]
variable {P : TopPair} {P' : TopPair}
open PairMap

open CategoryTheory in
structure HomotopyInvExcisionFunctor (R : Type*) [Ring R] extends Functor TopPair (ModuleCat R) where
  homotopy_inv : ∀ P P',  ∀ f f' : (P ⟶ P'), PairHomotopic f f' → (map f = map f')
  excision : ∀ P, ∀ U : Set (P.sub), IsIso (map (ExcisionInc P U))

-- the long exact sequence consisting of three parts

/-
instance (R: Type*) [Ring R] : Coe (HomotopyInvExcisionFunctor R) (Functor TopPair (ModuleCat R)) where
  coe := HomotopyInvExcisionFunctor.toFunctor
-/


@[simp]
lemma to_pair_total_eq_self {α : Type*} [TopologicalSpace α] : (toPair α).total = α := rfl

@[simp]
lemma to_pair_sub_eq_empty {α : Type*} [TopologicalSpace α] : (toPair α).sub = Empty := rfl


def ProjPairMap' (P : TopPair) : (toPair P.total) ⟶ P := ProjPairMap P

def IncPairMap' (P : TopPair) : (toPair P.sub) ⟶ (toPair P.total) where
  toFun := P.map
  continuous_toFun := Embedding.continuous P.isEmbedding
  image_sub := by
    simp [PairRangeSub, Set.range]

variable {F G : TopPair ⥤ ModuleCat R}
open CategoryTheory

structure InjProjExact (F : TopPair ⥤ ModuleCat R) (P : TopPair) : Prop where
  inj_proj_exact : Exact (F.map (IncPairMap' P)) (F.map (ProjPairMap' P))

-- an endofunctor of TopPair ` (α , β) ↦ (β, ∅)

def PairToSubFunctor : TopPair ⥤ TopPair where
  obj P := toPair P.sub
  map := by
    intro P P' f
    simp
    by_cases h: Nonempty P'.sub
    exact PairMapToSubPairMap f
    simp at h
    exact PairMapToSubPairMap' f
  map_id := by
    simp
    intro P
    split_ifs
    sorry
    sorry

  map_comp := sorry


#check dite_apply
-- example (α β: Type*) (h : IsEmpty α) : α → β := h.elim

structure BoundaryOp (F G : TopPair ⥤ ModuleCat R) extends NatTrans F (PairToSubFunctor ⋙ G)

structure ProjBoundExact {F G : TopPair ⥤ ModuleCat R} (bd :BoundaryOp F G) (P : TopPair) : Prop where
  inj_proj_exact : Exact (F.map (ProjPairMap' P)) (bd.app P)

structure BoundInjExact {F G : TopPair ⥤ ModuleCat R} (bd :BoundaryOp F G) (P : TopPair) : Prop where
  inj_proj_exact : Exact (bd.app P) (G.map (IncPairMap' P))

/-
define a coecion from HomotopyInvExcisionFunctor to Functor
-/


structure ExOrdHomology (R : Type*) [Ring R] where
  homology : ℤ → HomotopyInvExcisionFunctor R
  boundary_op (n : ℤ):  BoundaryOp (homology n).toFunctor (homology (n-1)).toFunctor
  exact_seq_inj_proj : ∀ n, ∀ P, InjProjExact (homology n).toFunctor P
  exact_seq_proj_bound : ∀ n, ∀ P, ProjBoundExact (boundary_op n) P
  exact_seq_bound_inj : ∀ n, ∀ P, BoundInjExact (boundary_op n) P


/-
  need zero functor
-/
/-
structure OrdHomology (R : Type*) [Ring R] extends ExOrdHomology R where
  dimension :
-/


/-
 def PairToSub : TopPair ⥤ TopPair where
  obj P := toPair P.sub
  map f := PairToSubMap f
  map_id := sorry
  map_comp := sorry
-/
/-
#check ContinuousMap
#check Functor
#check CategoryTheory.IsIso
#check ContinuousMap.Homotopy
#check Inducing
#check ModuleCat
#check continuous_id
#check Embedding
-- #check SemilinearMapClass
-/

#check Function.Injective
#check Function.invFun
