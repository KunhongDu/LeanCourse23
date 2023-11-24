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
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.CategoryTheory.ConcreteCategory.BundledHom


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

@[ext]
class PairMap (P₁ : TopPair α β) (P₂ : TopPair α' β') extends ContinuousMap α α' where
  image_in : ∀ b : β, ∃ b' : β', toFun (TopPair.map b) = TopPair.map b'
-- try set.range

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


protected def id : PairMap P P where
  toFun := id
  -- continuous_toFun := continuous_id
  -- I don't need this field why?
  image_in := by intro b; use b; simp

protected def comp (f : PairMap P' P'') (g : PairMap P P') : PairMap P P'' where
  toFun := f ∘ g
  image_in := by
    intro b
    obtain ⟨b', hb'⟩ := g.image_in b
    obtain ⟨b'', hb''⟩ := f.image_in b'
    use b''
    simp
    rw [← hb'] at hb''
    simp at hb''
    exact hb''

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

open CategoryTheory in
instance TopPairCategory : Category TopPairCat where
  Hom P Q := PairMap P.isTopPair Q.isTopPair
  id _ := PairMap.id
  comp f g := PairMap.comp g f
  id_comp _ := by simp
  comp_id _ := by simp
  assoc _ _ _ := by simp



#check Module
#check continuous_id
-- #check SemilinearMapClass
