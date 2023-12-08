-- add into the definition of pairmap a map between subspaces

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
structure TopPair where
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
  sub := ULift Empty
  isTotalTopologicalSpace := by infer_instance
  isSubTopologicalSpace := by infer_instance
  map := fun x ↦  isEmptyElim x
  isEmbedding := by simp [embedding_iff, inducing_iff, Function.Injective]

@[simp]
lemma to_pair_total_eq_self {α : Type*} [TopologicalSpace α]: (toPair α).total = α := rfl

@[simp]
lemma to_pair_sub_eq_empty {α : Type*} [TopologicalSpace α] : (toPair α).sub = Empty := rfl

@[simp]
lemma to_pair_map_empty_rec {α : Type*} [TopologicalSpace α]: (toPair α).map = Empty.rec := rfl

@[ext]
structure PairMap (P₁ : TopPair) (P₂ : TopPair) extends C(P₁.total, P₂.total) where
  sub_map : P₁.sub → P₂.sub
  comm : toFun ∘ P₁.map = P₂.map ∘ sub_map

namespace PairMap
variable {P P₁ P₂ P₃ : TopPair}

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

/-
class PairMapClass (F : Type*) {α β α' β' : Type*} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace α'] [TopologicalSpace β'] (P₁ : TopPair α β) (P₂ : TopPair α' β') extends ContinuousMapClass F α α'
-/

instance : ContinuousMapClass (PairMap P₁ P₂) P₁.total P₂.total where
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

-- toPair induces a PairMap

def toPairMap {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] (f : C(α, β)): PairMap (toPair α) (toPair β) where
  toFun := f
  continuous_toFun := by continuity
  sub_map := Empty.rec
  comm := by simp

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

def PairMapToSubPairMap (f : PairMap P₁ P₂) : PairMap (toPair P₁.sub) (toPair P₂.sub) where
  toFun := f.sub_map
  continuous_toFun := f.continuous_sub_map -- (by continuity does not work)
  sub_map := Empty.rec
  comm := by simp

@[simp]
lemma to_sub_pair_map_eq_sub_map {f : PairMap P₁ P₂} : (PairMapToSubPairMap f).toFun = f.sub_map := rfl

@[simp]
lemma id_to_sub_pair_map_eq_id : PairMapToSubPairMap (PairMap.id P) = PairMap.id (toPair P.sub) := by
  ext x
  simp at x
  simp

@[simp]
lemma to_sub_pair_map_comp {f : PairMap P₁ P₂} {g : PairMap P₂ P₃} : PairMapToSubPairMap (f ◾ g) = PairMapToSubPairMap f ◾ PairMapToSubPairMap g := by
  ext x
  simp

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

@[simp]
lemma excision_map_eq_self_map {P : TopPair} {U : Set P.sub} {x : (Uᶜ : Set P.sub)}: ((Excision P U).map x).1 = P.map x.1 := rfl

def ExcisionInc (P : TopPair) (U : Set P.sub) : PairMap (Excision P U) P where
  toFun := fun x ↦ x.1
  continuous_toFun := by continuity
  sub_map := fun x ↦ x.1
  comm := by ext; simp

/-
  Homotopy of pairs
-/

open ContinuousMap
/-
structure PairHomotopy (f₀ f₁ : PairMap P P') extends Homotopy (f₀ : C(α, α')) f₁ where
  always_image_sub : ∀ t, RangeSub ((fun x ↦ toFun (t, x)) ∘ P.map) P'.map
-/

structure PairHomotopy (f₀ f₁ : PairMap P₁ P₂) extends HomotopyWith (f₀ : C(P₁.total, P₂.total)) f₁ ContinuousMapExtendsToPairMap

def PairHomotopic (f₀ f₁ : PairMap P₁ P₂) : Prop :=
  Nonempty (PairHomotopy f₀ f₁)

@[ext]
structure PairHomotopyEquiv (P₁ : TopPair) (P₂ : TopPair) where
  toFun : PairMap P₁ P₂
  invFun : PairMap P₂ P₁
  left_inv : PairHomotopy (toFun.comp invFun) (PairMap.id P₁)
  right_inv : PairHomotopy (invFun.comp toFun) (PairMap.id P₂)

infixl:25 " ≃ₕ " => PairMap.PairHomotopyEquiv

#check P₁ ≃ₕ P₂



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
  id _ := PairMap.id _
  comp f g := PairMap.comp f g
  id_comp _ := by simp
  comp_id _ := by simp
  assoc _ _ _ := by simp

namespace TopPairegory
variable {P P₁ P₂ P₃ : TopPair}

@[simp]
lemma id_eq_pairmap_id {P : TopPair} : 𝟙 P = PairMap.id P := rfl

@[simp]
lemma comp_eq_pairmap_comp {P₁ P₂ P₃ : TopPair} {f : P₁ ⟶ P₂} {g : P₂ ⟶ P₃} : f ≫ g = PairMap.comp f g := rfl


end TopPairegory
/-
  Functor
-/

namespace Homology

structure IsTrivial {A R : Type*} [Ring R] [AddCommMonoid A] [Module R A] where
  isUnique : Unique A

/-
protected def trivial (R : Type*) [Ring R] : TopPair ⥤ ModuleCat R where
  obj := fun _ ↦
  map := _
  map_id := _
  map_comp := _
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


def ProjPairMap' (P : TopPair) : (toPair P.total) ⟶ P := ProjPairMap P

def IncPairMap' (P : TopPair) : (toPair P.sub) ⟶ (toPair P.total) where
  toFun := P.map
  continuous_toFun := Embedding.continuous P.isEmbedding
  sub_map := Empty.rec
  comm := by simp

variable {F G : TopPair ⥤ ModuleCat R}
open CategoryTheory

structure InjProjExact (F : TopPair ⥤ ModuleCat R) (P : TopPair) : Prop where
  inj_proj_exact : Exact (F.map (IncPairMap' P)) (F.map (ProjPairMap' P))

-- an endofunctor of TopPair ` (α , β) ↦ (β, ∅)

def PairToSubFunctor : TopPair ⥤ TopPair where
  obj P := toPair P.sub
  map := PairMapToSubPairMap
  map_id := by simp
  map_comp := by simp

#check ModuleCat R
#check dite_apply
-- example (α β: Type*) (h : IsEmpty α) : α → β := h.elim

abbrev BoundaryOp.{u₁, u₂, u₃} {R : Type u₃} [Ring R] (F: TopPair.{u₁, u₂} ⥤ ModuleCat R) (G: TopPair.{u₂, 0} ⥤ ModuleCat R) := NatTrans F (PairToSubFunctor ⋙ G)

#check BoundaryOp

structure ProjBoundExact {F G : TopPair ⥤ ModuleCat R} (bd :BoundaryOp F G) (P : TopPair) : Prop where
  inj_proj_exact : Exact (F.map (ProjPairMap' P)) (bd.app P)

structure BoundInjExact {F G : TopPair ⥤ ModuleCat R} (bd :BoundaryOp F G) (P : TopPair) : Prop where
  inj_proj_exact : Exact (bd.app P) (G.map (IncPairMap' P))

/-
define a coecion from HomotopyInvExcisionFunctor to Functor
-/
instance (α : Type*) [Unique α]: TopologicalSpace α := TopologicalSpace.generateFrom ⊤w

structure ExOrdHomology.{u₁, u₂} (R : Type u₁) [Ring R] where
  homology (n : ℤ): HomotopyInvExcisionFunctor R
  dimension (n : ℤ) (α : Type u₂) [Unique α] : Nontrivial ((homology n).obj (toPair α)) → n = 0
  boundary_op (n : ℤ) : BoundaryOp (homology n).toFunctor (homology (n-1)).toFunctor

#check

/-
  boundary_op (n : ℤ) : BoundaryOp (homology n).toFunctor (homology (n-1)).toFunctor
  exact_seq_inj_proj : ∀ n, ∀ P, InjProjExact (homology n).toFunctor P
  exact_seq_proj_bound : ∀ n, ∀ P, ProjBoundExact (boundary_op n) P
  exact_seq_bound_inj : ∀ n, ∀ P, BoundInjExact (boundary_op n) P


variable {F : HomotopyInvExcisionFunctor R} (α : Type*) [Unique α] {H : ExOrdHomology R}

instance (α : Type*) [Unique α]: TopologicalSpace α := TopologicalSpace.generateFrom ⊤

#check (H.homology 0).obj (toPair α)

structure OrdHomology (R : Type*) [Ring R] extends ExOrdHomology R where
  dimension (n : ℤ) (α : Type*) [Unique α] : Nontrivial ((homology n).obj (toPair α)) → n = 0

/-
structure test (R : Type*) [Ring R] {F : HomotopyInvExcisionFunctor R} (α : Type*) [Unique α] where
  dimension (n : ℤ) (α : Type*) [Unique α] : Nontrivial (F.obj (toPair α)) → n = 0
-/

/-
  additivity
-/

#check @Sigma.mk
#check instTopologicalSpaceSigma


def SigmaTopPair {ι : Type*} (P : ι → TopPair) : TopPair where
  total := Σ i, (P i).total
  sub :=  Σ i, (P i).sub
  isTotalTopologicalSpace := by infer_instance
  isSubTopologicalSpace := by infer_instance
  map := Sigma.map id (fun i a ↦ (@TopPair.map (P i)) a)
  isEmbedding := sorry

def SigmaTopPairInc {ι : Type*} (P : ι → TopPair) (i : ι) : PairMap (P i) (SigmaTopPair P) where
  toFun := fun a ↦ ⟨i, a⟩
  continuous_toFun := continuous_iSup_rng continuous_coinduced_rng
  sub_map := fun a ↦ ⟨i, a⟩
  comm := sorry


structure AddHomology {R : Type*} [Ring R] (F : TopPair ⥤ ModuleCat R) where
  additivity {ι : Type*} (P : ι → TopPair) (i : ι): IsIso (F.map (SigmaTopPairInc P i))



/-
example {α : Type u} {β : α → Type v} [t₂ : (a : α) → TopologicalSpace (β a)] :
TopologicalSpace (Σ a, β a) := by infer_instance

example {ι : Type u} (A : ι → Type u) [(i : ι) → AddCommMonoid (A i)] [(i : ι) → Module R (A i)] : Module R ( ⨁ (i : ι), A i ) := by infer_instance
-/






#check ContinuousMap
#check Functor
#check CategoryTheory.IsIso
#check ContinuousMap.Homotopy
#check Inducing
#check ModuleCat
#check continuous_id
#check Embedding
-- #check SemilinearMapClass


#check Function.Injective
#check Function.invFun
#check ModuleCat
-/
-/
