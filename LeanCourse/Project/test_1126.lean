import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.Homotopy.Equiv
import Mathlib.CategoryTheory.ConcreteCategory.BundledHom
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.Exact
noncomputable section

#check TopologicalSpace

universe u v w
variable {α β α' β' α'' β'': Type*}
variable [TopologicalSpace α]  [TopologicalSpace β] [TopologicalSpace α'] [TopologicalSpace β'] [TopologicalSpace α''] [TopologicalSpace β'']

@[ext]
class TopPair (α β : Type*) [TopologicalSpace α] [TopologicalSpace β] where
  map : β  → α
  isEmbedding : Embedding map

-- coersion

#check instTopologicalSpaceEmpty

/-
instance emptyTop : TopologicalSpace Empty where
  IsOpen := fun _ ↦ true
  isOpen_univ := rfl
  isOpen_inter := fun _ _ a _ ↦ a
  isOpen_sUnion := fun _ _ ↦ rfl
-/

/-- ` toPair ` sends a topological space ` α ` to a topological pair ` (α, ∅) `
-/
def toPair (α : Type*) [TopologicalSpace α]: TopPair α Empty where
  map := Empty.rec
  isEmbedding := by simp [embedding_iff, inducing_iff, Function.Injective]


def PairRangeSub (P₁ : TopPair α β) (P₂ : TopPair α' β') (f : C(α, α')) : Prop :=
  Set.range (f ∘ P₁.map) ⊆ Set.range P₂.map

@[ext]
class PairMap (P₁ : TopPair α β) (P₂ : TopPair α' β') extends ContinuousMap α α' where
  image_sub : PairRangeSub P₁ P₂ (ContinuousMap.mk toFun)

/-
class PairMapClass (F : Type*) {α β α' β' : Type*} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace α'] [TopologicalSpace β'] (P₁ : TopPair α β) (P₂ : TopPair α' β') extends ContinuousMapClass F α α'
-/

namespace PairMap
variable {P : TopPair α β} {P' : TopPair α' β'} {P'' : TopPair α'' β''}

instance : ContinuousMapClass (PairMap P P') α α' where
  coe := fun f ↦ f.toFun
  coe_injective' := by
    intro f f' h
    ext1
    exact h
  map_continuous := fun f ↦ f.continuous

lemma PairMapImageSub {P₁ : TopPair α β} {P₂ : TopPair α' β'} (f : PairMap P₁ P₂) : ∀ b : β, ∃ b' : β', TopPair.map b' = f (TopPair.map b) := by
  have : PairRangeSub P₁ P₂ f := f.image_sub
  simp [PairRangeSub, Set.range] at this
  exact this

/-
example (f : α → β) (g : β → β) : Set.range (g ∘ f) ⊆ Set.range (g) := by exact Set.range_comp_subset_range f g

example (f : α → β) (A B : Set α) (h : A ⊆ B): f '' A ⊆ f '' B := by exact
  Set.image_subset f h
-/
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
    calc range ((↑f ∘ ↑g) ∘ TopPair.map) = range (↑f ∘ (↑g ∘ P.map)) := rfl
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
theorem comp_assoc {α''' β''' :  Type*} [TopologicalSpace α'''] [TopologicalSpace β'''] {P''' : TopPair α''' β'''} (f'' : PairMap P'' P''') (f' : PairMap P' P'') (f : PairMap P P') :
  PairMap.comp (PairMap.comp f'' f') f = PairMap.comp f'' (PairMap.comp f' f) := by ext; simp

-- Define a pair map ` X = (X, ∅) → (X, A) `, whose role in the long exact sequence is comparable a projection, so I'll call it so

def ProjPairMap (P : TopPair α β) : PairMap (toPair α) P where
  toFun := id
  continuous_toFun := by continuity
  image_sub := by simp [PairRangeSub, Set.range];

-- A pair map induced a map between the subspaces


def PairMapToSubMap [Nonempty β'] (f : PairMap P P') : C(β, β') where
  toFun :=  Function.invFun (P'.map) ∘ f ∘ P.map
  continuous_toFun := by
    apply (Embedding.continuous_iff P'.isEmbedding).mpr
    have : P'.map ∘ Function.invFun (P'.map) ∘ f ∘ P.map = f ∘ P.map := by
      ext b
      obtain ⟨y, hy⟩ := PairMapImageSub f b
      simp [← hy]
      exact Function.apply_invFun_apply
    rw [this]
    apply Continuous.comp (by continuity) (Embedding.continuous P.isEmbedding)


-- Define the operation of excision

-- Subspace topology is already define
-- subtype not subset nor subspace
#check instTopologicalSpaceSubtype
variable (U : Set β) (V : Set α)

#check Set.inclusion

/-
failed to synthesize instance
  HasCompl (Type u_1)

def Excision : TopPair (P.map '' U)ᶜ  Uᶜ := by sorry
-/

lemma excision_is_in (x : (Uᶜ : Set β)) : P.map (x : β)  ∈ (P.map '' U)ᶜ := by
  intro h
  obtain ⟨x', hx'1, hx'2⟩ := h
  apply @(P.isEmbedding.inj) at hx'2
  have : (x : β) ∈ Uᶜ := x.2 --- omg!!!
  rw [← hx'2] at this
  exact this hx'1


def Excision (P : TopPair α β) (U : Set β) : TopPair ((P.map '' U)ᶜ : Set α)   (Uᶜ : Set β) where
  map := fun x ↦ (⟨P.map x, excision_is_in _ _⟩ : ((P.map '' U)ᶜ : Set α))
  isEmbedding := by
    simp [embedding_iff, Function.Injective]
    constructor
    . sorry
    . intro _ _ _ _ hab
      apply P.isEmbedding.inj hab

-- restriction is inducing...


def ExcisionInc (P : TopPair α β) (U : Set β) : PairMap (Excision P U) P where
  toFun := fun x ↦ (x : α)
  continuous_toFun := by continuity
  image_sub := by
    simp [PairRangeSub, Set.range]
    intro _ x _ h
    exact ⟨x , h⟩




/-
  Homotopy of pairs
-/

open ContinuousMap
/-
structure PairHomotopy (f₀ f₁ : PairMap P P') extends Homotopy (f₀ : C(α, α')) f₁ where
  always_image_sub : ∀ t, RangeSub ((fun x ↦ toFun (t, x)) ∘ P.map) P'.map
-/

structure PairHomotopy (f₀ f₁ : PairMap P P') extends HomotopyWith (f₀ : C(α, α')) f₁ (PairRangeSub P P')

def PairHomotopic (f₀ f₁ : PairMap P P') : Prop :=
  Nonempty (PairHomotopy f₀ f₁)

@[ext]
structure PairHomotopyEquiv (P : TopPair α β) (P' : TopPair α' β') where
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
structure TopPairCat where
  total : Type u
  sub : Type v
  isTotalTopologicalSpace : TopologicalSpace total
  isSubTopologicalSpace : TopologicalSpace sub
  isTopPair : TopPair total sub

attribute [instance] TopPairCat.isTotalTopologicalSpace TopPairCat.isSubTopologicalSpace TopPairCat.isTopPair

/-
variable {C : TopPairCat}
instance : CoeDep TopPairCat C (TopPair C.total C.sub) where
  coe := C.isTopPair
-/

open CategoryTheory

instance TopPairCategory : Category TopPairCat where
  Hom P Q := PairMap P.isTopPair Q.isTopPair
  id _ := PairMap.id
  comp f g := PairMap.comp g f
  id_comp _ := by simp
  comp_id _ := by simp
  assoc _ _ _ := by simp

/-
  Functor
-/

variable (R : Type*) [Ring R]
variable {P : TopPairCat} {P' : TopPairCat}
open PairMap

def Excision' (P : TopPairCat) (U : Set (P.sub)) : TopPairCat where
  total := ((P.isTopPair.map '' U)ᶜ : Set (P.total))
  sub := (Uᶜ : Set (P.sub))
  isTotalTopologicalSpace := by infer_instance
  isSubTopologicalSpace := by infer_instance
  isTopPair := Excision P.isTopPair U

def ExcisionInc' (P : TopPairCat) (U : Set (P.sub)) : (Excision' P U) ⟶ P := ExcisionInc P.isTopPair U

open CategoryTheory in
structure HomotopyInvExcisionFunctor extends Functor TopPairCat (ModuleCat R) where
  homotopy_inv : ∀ f f' : (P ⟶ P'), PairHomotopic f f' → (map f = map f')
  excision : ∀ U : Set (P.sub), IsIso (map (ExcisionInc' P U))

-- the long exact sequence consisting of three parts

def toPair' (α : Type*) [TopologicalSpace α] : TopPairCat where
  total := α
  sub := Empty
  isTotalTopologicalSpace := by infer_instance
  isSubTopologicalSpace := by infer_instance
  isTopPair := toPair α

@[simp]
lemma to_pair_total_eq_self {α : Type*} [TopologicalSpace α] : (toPair' α).total = α := rfl

@[simp]
lemma to_pair_sub_eq_empty {α : Type*} [TopologicalSpace α] : (toPair' α).sub = Empty := rfl


def ProjPairMap' (P : TopPairCat) : (toPair' P.total) ⟶ P := ProjPairMap P.isTopPair

def IncPairMap' (P : TopPairCat) : (toPair' P.sub) ⟶ (toPair' P.total) where
  toFun := P.isTopPair.map
  continuous_toFun := Embedding.continuous P.isTopPair.isEmbedding
  image_sub := by
    simp [PairRangeSub, Set.range]

variable (F G : TopPairCat ⥤ ModuleCat R)

open CategoryTheory

structure InjProjExact (P : TopPairCat) : Prop where
  inj_proj_exact : Exact (F.map (IncPairMap' P)) (F.map (ProjPairMap' P))

-- an endofunctor of TopPairCat ` (α , β) ↦ (β, ∅)


def PairMapToSubMap' {P P': TopPairCat} (f : P ⟶ P') : toPair' P.sub ⟶ toPair' P'.sub where
  toFun := by
    sorry
  image_sub := by
    simp [PairRangeSub, Set.range]

-- def PairToSubMap {P P': TopPairCat} (f : P ⟶ P') : toPair' P.sub ⟶ toPair' P'.sub where
--  toFun := by
-/



/-
 def PairToSub : TopPairCat ⥤ TopPairCat where
  obj P := toPair' P.sub
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
