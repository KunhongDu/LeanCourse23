import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.Homotopy.Equiv
import Mathlib.CategoryTheory.ConcreteCategory.BundledHom
import Mathlib.Algebra.Category.ModuleCat.Basic

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


-- define the operation of excision

#check Set.inclusion
#check TopologicalSpace.induced
#check continuous_induced_dom
-- maybe first define a structure of subspace?

example (U : Set α) : U ⊆ Set.univ := by exact Set.subset_univ U

-- example (U : Set α) : U → α :=



/-
open TopologicalSpace in
structure TopSubspace (α : Type*) [TopologicalSpace α] where
  carrier : Set α
  inclusion := fun u : carrier ↦ (u : α)
  topology := induced inclusion (by infer_instance)
  continuity : Continuous inclusion := by continuity
  inclusion' := ContinuousMap.mk inclusion
  -- continuous_induced_dom does not work, which should be the theorem ` continuity ` has referred to
  -- also ` by exact [something] ` does not work
  -- gives ` invalid auto tactic, identifier is not allowed `
-/
/-
structure TopSubspace (α : Type*) [TopologicalSpace α] where
  carrier : Set α
  inclusion : carrier → α
  topology : TopologicalSpace carrier
  continuity : Continuous inclusion
  inclusion' : C(carrier, α)

open TopologicalSpace in
instance (U : Set α) : TopSubspace α where
  carrier := U
  inclusion := fun u : U ↦ (u : α)
  topology := induced (fun u : U ↦ (u : α)) (by infer_instance)
  continuity := by continuity
  inclusion' := ContinuousMap.mk (fun u : U ↦ (u : α))
-/
variable {U : Set α}



-- #check TopSubspace.mk


/-
def PairRangeSub (P₁ : TopPair α β) (P₂ : TopPair α' β') (f : C(α, α')) : Prop :=
  Set.range (f ∘ P₁.map) ⊆ Set.range P₂.map

@[ext]
class PairMap (P₁ : TopPair α β) (P₂ : TopPair α' β') extends ContinuousMap α α' where
  image_sub : PairRangeSub P₁ P₂ (ContinuousMap.mk toFun)

#check PairMap.toContinuousMap

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
theorem comp_assoc {α''' β''' :  Type u} [TopologicalSpace α'''] [TopologicalSpace β'''] {P''' : TopPair α''' β'''} (f'' : PairMap P'' P''') (f' : PairMap P' P'') (f : PairMap P P') :
  PairMap.comp (PairMap.comp f'' f') f = PairMap.comp f'' (PairMap.comp f' f) := by ext; simp

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
  sub : Type u
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
open PairMap in
structure ExOrdHomology extends Functor TopPairCat (ModuleCat R) where
  homotopy_inv : ∀ f f' : (P ⟶ P'), PairHomotopic f f' → (map f = map f')


#check ContinuousMap.Homotopy
#check Inducing
#check ModuleCat
#check continuous_id
-- #check SemilinearMapClass
-/
