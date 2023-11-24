import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.CategoryTheory.ConcreteCategory.BundledHom


#check TopologicalSpace

universe u v w

@[ext]
class TopPair (α β : Type*) [TopologicalSpace α] [TopologicalSpace β] where
  map : β  → α
  isEmbedding : Embedding map

-- coersion

variable {α : Type*} {β : Type*} {α' : Type*} {β' : Type*} {α'' : Type*} {β'' : Type*}
variable [TopologicalSpace α]  [TopologicalSpace β] [TopologicalSpace α'] [TopologicalSpace β'] [TopologicalSpace α''] [TopologicalSpace β'']

@[ext]
class PairMap (P₁ : TopPair α β) (P₂ : TopPair α' β') extends ContinuousMap α α' where
  image_in : ∀ b : β, ∃ b' : β', toFun (TopPair.map b) = TopPair.map b'

#check PairMap.toContinuousMap


/-
class PairMapClass (F : Type*) {α β α' β' : Type*} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace α'] [TopologicalSpace β'] (P₁ : TopPair α β) (P₂ : TopPair α' β') extends ContinuousMapClass F α α'
-/

namespace PairMap
variable {P : TopPair α β} {P' : TopPair α' β'} {P'' : TopPair α'' β''}

protected def id : PairMap P P where
  toFun := id
  -- continuous_toFun := continuous_id
  -- I don't need this field why?
  image_in := by intro b; use b; simp

protected def comp (f : PairMap P' P'') (g : PairMap P P') : PairMap P P'' where
  toFun := f.toFun ∘ g.toFun
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



/-
  Category
-/

structure TopPairCat where
  carrier : Type u




open CategoryTheory in
instance TopPairCategory : Category TopPairCat := by sorry
  -- Hom P Q := by sorry
  -- id := by sorry
  -- comp := by sorry




#check continuous_id
