import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.CategoryTheory.ConcreteCategory.BundledHom
import Mathlib.Algebra.Category.ModuleCat.Basic

#check TopologicalSpace

-- I decide to require them to be in the same universe
universe u v w
variable {α β α' β' α'' β'': Type*}
variable [TopologicalSpace α]  [TopologicalSpace β] [TopologicalSpace α'] [TopologicalSpace β'] [TopologicalSpace α''] [TopologicalSpace β'']

@[ext]
class TopPair (α β : Type*) [TopologicalSpace α] [TopologicalSpace β] where
  map : β  → α
  isEmbedding : Embedding map

-- coersion

#check Empty

instance emptyTop : TopologicalSpace Empty where
  IsOpen := fun _ ↦ true
  isOpen_univ := rfl
  isOpen_inter := fun _ _ a _ ↦ a
  isOpen_sUnion := fun _ _ ↦ rfl

def toPair (α : Type*) [TopologicalSpace α]: TopPair α Empty where
  map := Empty.rec
  isEmbedding := by simp [embedding_iff, inducing_iff, Function.Injective]

def RangeSub {α β γ : Type*} (f : α → γ) (g : β → γ) : Prop :=
  Set.range f ⊆ Set.range g

@[ext]
class PairMap (P₁ : TopPair α β) (P₂ : TopPair α' β') extends ContinuousMap α α' where
  image_sub : RangeSub (toFun ∘ P₁.map) P₂.map

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

-- structure ExOrdHomology extends Functor TopPairCat (ModuleCat R) where


#check ModuleCat
#check continuous_id
-- #check SemilinearMapClass
