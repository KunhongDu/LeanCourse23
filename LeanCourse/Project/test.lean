import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.CategoryTheory.ConcreteCategory.BundledHom


#check TopologicalSpace

universe u v w
variable {α : Type u} {β : Type u} {α' : Type u} {β' : Type u}


@[ext]
structure TopPair (α β : Type u) where
  map : β  → α
  TotalTop : TopologicalSpace α
  SubTop : TopologicalSpace β
  isEmbedding : Embedding map

-- if you use class above, the following doesn't work
attribute [instance] TopPair.TotalTop TopPair.SubTop

structure TopPairCat where
  total : Type u
  sub : Type u
  [isTopPair : TopPair total sub]

attribute [instance] TopPairCat.isTopPair

structure PairMap (P₁ : TopPair α β) (P₂ : TopPair α' β') extends ContinuousMap α β


open CategoryTheory in
instance TopPairCategory : Category TopPairCat := by sorry
  -- Hom P Q := by sorry
  -- id := by sorry
  -- comp := by sorry

#check MonoidHom
