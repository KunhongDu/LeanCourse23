import LeanCourse.Common
import Mathlib.Topology.Instances.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open BigOperators Function Set Filter Topology TopologicalSpace MeasureTheory
noncomputable section
set_option linter.unusedVariables false
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)


/- # Today: Topology

We cover chapter 9 from Mathematics in Lean. -/

/-
Last time we discussed abstract algebra.
-/







/- # Limits -/


/-
In topology, one of basic concepts is that of a limit.
Say `f : ℝ → ℝ`. There are many variants of limits.
* the limit of `f(x)` as `x` tends to `x₀`
* the limit of `f(x)` as `x` tends to `∞` or `-∞`
* the limit of `f(x)` as `x` tends to `x₀⁻` or `x₀⁺`
* variations of the above with the additional assumption that `x ≠ x₀`.

This gives 8 different notions of behavior of `x`.
Similarly, the value `f(x)` can have the same behavior:
`f(x)` tends to `∞`, `-∞`, `x₀`, `x₀⁺`, ...

This gives `64` notions of limits.

When we prove that two limits compose: if
`f x` tends to `y₀` when `x` tends to `x₀` and
`g y` tends to `z₀` when `y` tends to `y₀` then
`(g ∘ f) x` tends to `z₀` when `x` tends to `x₀`.
This lemma has 512 variants.

Obviously we don't want to prove this 512 times.
Solution: use filters.










If `X` is a type, a filter `F : Filter X` is a
collection of sets `F.sets : Set (Set X)` satisfying the following:
-/
section Filter

variable {X Y : Type*} (F : Filter X)

#check (F.sets : Set (Set X))
#check (F.univ_sets : univ ∈ F.sets)
#check (F.sets_of_superset : ∀ {U V},
  U ∈ F.sets → U ⊆ V → V ∈ F.sets)
#check (F.inter_sets : ∀ {U V},
  U ∈ F.sets → V ∈ F.sets → U ∩ V ∈ F.sets)
end Filter






/-
Examples of filters:
-/

/- `(atTop : Filter ℕ)` is made of sets of `ℕ` containing
`{n | n ≥ N}` for some `N` -/
#check (atTop : Filter ℕ)

/- `𝓝 x`, made of neighborhoods of `x` in a topological space -/
#check (𝓝 3 : Filter ℝ)

/- `μ.ae` is made of sets whose complement has zero measure with respect to a measure `μ`. -/
#check (volume.ae : Filter (ℝ × ℝ × ℝ))

/-
It may be useful to think of a filter on a type `X`
as a generalized element of `Set X`.
* `atTop` is the "set of very large numbers"
* `𝓝 x₀` is the "set of points very close to `x₀`."
* For each `s : Set X` we have the so-called *principal filter*
  `𝓟 s` consisting of all sets that contain `s` (exercise!).
-/






/- Operations on filters -/

/- the *pushforward* of filters generalizes images of sets. -/
example {X Y : Type*} (f : X → Y) : Filter X → Filter Y :=
  Filter.map f

example {X Y : Type*} (f : X → Y) (F : Filter X) (V : Set Y) :
    V ∈ Filter.map f F ↔ f ⁻¹' V ∈ F := by
  rfl

/- the *pullback* of filters generalizes preimages -/
example {X Y : Type*} (f : X → Y) : Filter Y → Filter X :=
  Filter.comap f

/- These form a *Galois connection* / adjunction -/
example {X Y : Type*} (f : X → Y) (F : Filter X) (G : Filter Y) :
    Filter.map f F ≤ G ↔ F ≤ Filter.comap f G := by
  exact map_le_iff_le_comap

/- `Filter X` has an order that turns it into a complete lattice. The order is reverse inclusion: -/
example {X : Type*} (F F' : Filter X) :
    F ≤ F' ↔ ∀ V : Set X, V ∈ F' → V ∈ F := by
  rfl

/- This makes the principal filter `𝓟 : Set X → Filter X` monotone. -/
example {X : Type*} : Monotone (𝓟 : Set X → Filter X) := by
  exact monotone_principal







/- Using these operations, we can define the limit. -/
def MyTendsto {X Y : Type*} (f : X → Y)
    (F : Filter X) (G : Filter Y) :=
  map f F ≤ G

def Tendsto_iff {X Y : Type*} (f : X → Y)
    (F : Filter X) (G : Filter Y) :
    Tendsto f F G ↔ ∀ S : Set Y, S ∈ G → f ⁻¹' S ∈ F := by
  rfl

/- A sequence `u` converges to `x` -/
example (u : ℕ → ℝ) (x : ℝ) : Prop :=
  Tendsto u atTop (𝓝 x)

/- `\lim_{x → x₀} f(x) = y₀` -/
example (f : ℝ → ℝ) (x₀ y₀ : ℝ) : Prop :=
  Tendsto f (𝓝 x₀) (𝓝 y₀)

/- `\lim_{x → x₀⁻, x ≠ x₀} f(x) = y₀⁺` -/
example (f : ℝ → ℝ) (x₀ y₀ : ℝ) : Prop :=
  Tendsto f (𝓝[<] x₀) (𝓝[≥] y₀)

/- Now the following states all possible composition lemmas all at
once! -/
example {X Y Z : Type*} {F : Filter X} {G : Filter Y} {H : Filter Z}
    {f : X → Y} {g : Y → Z}
    (hf : Tendsto f F G) (hg : Tendsto g G H) :
    Tendsto (g ∘ f) F H :=
  fun _ hS ↦ hf (hg hS)


   /- # Exercise -/

/-
Filters also allow us to reason about things that are
"eventually true". If `F : Filter X` and `P : X → Prop` then
`∀ᶠ n in F, P n` means that `P n` is eventually true for `n` in `F`.
It is defined to be `{ x | P x } ∈ F`.

The following example shows that if `P n` and `Q n` hold for
sufficiently large `n`, then so does `P n ∧ Q n`.
-/
example (P Q : ℕ → Prop)
    (hP : ∀ᶠ n in atTop, P n)
    (hQ : ∀ᶠ n in atTop, Q n) :
    ∀ᶠ n in atTop, P n ∧ Q n :=
  hP.and hQ








section Topology

/- Let's look at the definition of topological space. -/

variable {X : Type*} [TopologicalSpace X]
variable {Y : Type*} [TopologicalSpace Y]


example {ι : Type*} (s : ι → Set X) : interior (⋂ i, s i) ⊆ ⋂ i, interior (s i) := by
  simp -- subset_iInter_iff
  intro i
  apply interior_mono
  exact iInter_subset (fun i ↦ s i) i

example {ι Z : Type*} (s : ι → Set Z) (a : Set Z): a ⊆ ⋂ i, s i ↔ ∀ i, a ⊆ s i :=
by exact subset_iInter_iff


/- A map between topological spaces is continuous if the
preimages of open sets are open. -/
example {f : X → Y} :
    Continuous f ↔ ∀ s, IsOpen s → IsOpen (f ⁻¹' s) :=
  continuous_def

/- It is equivalent to saying that for any `x₀` the function
value `f x` tends to `f x₀` whenever `x` tends to `x₀`. -/
example {f : X → Y} :
    Continuous f ↔ ∀ x₀, Tendsto f (𝓝 x₀) (𝓝 (f x₀)) := by
  exact continuous_iff_continuousAt

/- By definition, the right-hand side states that `f` is
continuous at `x₀`. -/
example {f : X → Y} {x₀ : X} :
    ContinuousAt f x₀ ↔ Tendsto f (𝓝 x₀) (𝓝 (f x₀)) := by
  rfl







/- Neighborhoods are characterized by the following lemma. -/
example {x : X} {s : Set X} :
    s ∈ 𝓝 x ↔ ∃ t, t ⊆ s ∧ IsOpen t ∧ x ∈ t :=
  mem_nhds_iff

example {x : X} {s : Set X} (h : s ∈ 𝓝 x) : x ∈ s := by
  exact mem_of_mem_nhds h





/- We can state that a topological space satisfies
  separatedness axioms. -/

example : T0Space X ↔ Injective (𝓝 : X → Filter X) := by
  exact t0Space_iff_nhds_injective X

example : T1Space X ↔ ∀ x, IsClosed ({ x } : Set X) :=
  ⟨by exact fun a x ↦ T1Space.t1 x, by exact fun a ↦ { t1 := a }⟩

example : T2Space X ↔
    ∀ x y : X, x ≠ y → Disjoint (𝓝 x) (𝓝 y) := by
  exact t2Space_iff_disjoint_nhds

example : RegularSpace X ↔ ∀ {s : Set X} {a},
    IsClosed s → a ∉ s → Disjoint (𝓝ˢ s) (𝓝 a) := by
  exact regularSpace_iff X









/- A set is compact if every open cover has a finite subcover. -/

example {K : Set X} : IsCompact K ↔ ∀ {ι : Type _}
    (U : ι → Set X), (∀ i, IsOpen (U i)) → (K ⊆ ⋃ i, U i) →
    ∃ t : Finset ι, K ⊆ ⋃ i ∈ t, U i := by
  exact isCompact_iff_finite_subcover

/-
This can also be reformulated using filters.
* `NeBot F` iff `F ≠ ⊥` iff `∅ ∉ F`
* `ClusterPt x F` means that `F` has nontrivial intersection
  with `𝓝 x` (viewed as a generalized sets).
* `K` is compact iff every nontrivial filter that contains `K`
  has a cluster point in `K`.
-/

example (F : Filter X) : NeBot F ↔ F ≠ ⊥ := by
  exact neBot_iff

example {x : X} (F : Filter X) :
    ClusterPt x F ↔ NeBot (𝓝 x ⊓ F) := by
  rfl

example {K : Set X} : IsCompact K ↔
    ∀ {F} [NeBot F], F ≤ 𝓟 K → ∃ x ∈ K, ClusterPt x F := by
  rfl

end Topology














section Metric

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

/- A metric space is a type `X` equipped with a distance function `dist : X → X → ℝ` with the following properties. -/

#check (dist : X → X → ℝ)
#check (dist_nonneg : ∀ {a b : X}, 0 ≤ dist a b)
#check (dist_eq_zero : ∀ {a b : X}, dist a b = 0 ↔ a = b)
#check (dist_comm : ∀ (a b : X), dist a b = dist b a)
#check (dist_triangle : ∀ (a b c : X), dist a c ≤ dist a b + dist b c)

/- In metric spaces, all topological notions are also
characterized by the distance function. -/

example (f : X → Y) (x₀ : X) : ContinuousAt f x₀ ↔
    ∀ ε > 0, ∃ δ > 0, ∀ {x},
    dist x x₀ < δ → dist (f x) (f x₀) < ε :=
  Metric.continuousAt_iff

example (x : X) (ε : ℝ) :
    Metric.ball x ε = { y | dist y x < ε } := by
  rfl

example (s : Set X) :
    IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, Metric.ball x ε ⊆ s :=
  Metric.isOpen_iff

end Metric




/- # Exercises

The goal of these exercise is to prove that
the regular open sets in a topological space form a complete boolean algebra.
`U ⊔ V` is given by `interior (closure (U ∪ V))`.
`U ⊓ V` is given by `U ∩ V`. -/


variable {X : Type*} [TopologicalSpace X]

variable (X) in
structure RegularOpens where
  carrier : Set X
  isOpen : IsOpen carrier
  regular' : interior (closure carrier) = carrier

namespace RegularOpens

/- We write some lemmas so that we can easily reason about regular open sets. -/
variable {U V : RegularOpens X}

instance : SetLike (RegularOpens X) X where
  coe := RegularOpens.carrier
  coe_injective' := fun ⟨_, _, _⟩ ⟨_, _, _⟩ _ => by congr

theorem le_def {U V : RegularOpens X} : U ≤ V ↔ (U : Set X) ⊆ (V : Set X) := by simp
@[simp] theorem regular {U : RegularOpens X} : interior (closure (U : Set X)) = U := U.regular'

@[simp] theorem carrier_eq_coe (U : RegularOpens X) : U.1 = ↑U := rfl

@[ext] theorem ext (h : (U : Set X) = V) : U = V :=
  SetLike.coe_injective h


/- First we want a complete lattice structure on the regular open sets.
We can obtain this from a so-called `GaloisCoinsertion` with the closed sets.
This is a pair of maps
* `l : RegularOpens X → Closeds X`
* `r : Closeds X → RegularOpens X`
with the properties that
* for any `U : RegularOpens X` and `C : Closeds X` we have `l U ≤ C ↔ U ≤ r U`
* `r ∘ l = id`
If you know category theory, this is an *adjunction* between orders
(or more precisely, a coreflection).
-/

/- The closure of a regular open set. Of course mathlib knows that the closure of a set is closed.
(the `simps` attribute will automatically generate the simp-lemma for you that
`(U.cl : Set X) = closure (U : Set X)`
-/
@[simps]
def cl (U : RegularOpens X) : Closeds X :=
  ⟨closure U, isClosed_closure⟩

/- The interior of a closed set. You will have to prove yourself that it is regular open. -/

example (C: Set X) (h: IsClosed C) : closure C =  C := by exact IsClosed.closure_eq h

lemma int_cl_int_eq_int {C: Set X} (h: IsClosed C) : interior (closure (interior C)) = interior C := by
    apply subset_antisymm
    . apply interior_mono
      nth_rw 2 [← IsClosed.closure_eq h]
      apply closure_mono
      exact interior_subset
    . apply interior_maximal subset_closure isOpen_interior

#check interior_maximal

@[simps]
def _root_.TopologicalSpace.Closeds.int (C : Closeds X) : RegularOpens X :=
  ⟨interior C, isOpen_interior, int_cl_int_eq_int C.2⟩


/- Now let's show the relation between these two operations. -/
lemma cl_le_iff {U : RegularOpens X} {C : Closeds X} :
    U.cl ≤ C ↔ U ≤ C.int := by
    constructor
    . intro h
      apply interior_mono at h
      simp at h -- rw does not work
      exact h
    . intro h
      apply closure_mono at h
      apply Subset.trans h
      simp
      nth_rw 2 [← IsClosed.closure_eq C.closed] -- only work after simp
      apply closure_mono
      exact interior_subset

example (C D E: Set X) (h : C ⊆ D) (h' : D ⊆ E) : C ⊆ E := by exact Subset.trans h h'


@[simp] lemma cl_int : U.cl.int = U := by
  ext
  simp -- ah??? why???

/- This gives us a GaloisCoinsertion. -/

def gi : GaloisCoinsertion cl (fun C : Closeds X ↦ C.int) where
  gc U C := cl_le_iff
  u_l_le U := by simp
  choice C hC := C.int
  choice_eq C hC := rfl

/- It is now a general theorem that we can lift the complete lattice structure from `Closeds X`
to `RegularOpens X`. The lemmas below give the definitions of the lattice operations. -/
--

instance completeLattice : CompleteLattice (RegularOpens X) :=
  GaloisCoinsertion.liftCompleteLattice gi

@[simp] lemma coe_inf {U V : RegularOpens X} : ↑(U ⊓ V) = (U : Set X) ∩ V := by
  have : U ⊓ V = (U.cl ⊓ V.cl).int := rfl
  simp [this]

@[simp] lemma coe_sup {U V : RegularOpens X} : ↑(U ⊔ V) = interior (closure ((U : Set X) ∪ V)) := by
  have : U ⊔ V = (U.cl ⊔ V.cl).int := rfl
  simp [this]

@[simp] lemma coe_top : ((⊤ : RegularOpens X) : Set X) = univ := by
  have : (⊤ : RegularOpens X) = (⊤ : Closeds X).int := rfl
  simp [this]

@[simp] lemma coe_bot : ((⊥ : RegularOpens X) : Set X) = ∅ := by
  have : (⊥ : RegularOpens X) = (⊥ : Closeds X).int := rfl
  simp [this]

@[simp] lemma coe_sInf {U : Set (RegularOpens X)} :
    ((sInf U : RegularOpens X) : Set X) =
    interior (⋂₀ ((fun u : RegularOpens X ↦ closure u) '' U)) := by
  have : sInf U = (sInf (cl '' U)).int := rfl
  simp [this]

@[simp] lemma Closeds.coe_sSup {C : Set (Closeds X)} : ((sSup C : Closeds X) : Set X) =
    closure (⋃₀ ((↑) '' C)) := by
  have : sSup C = Closeds.closure (sSup ((↑) '' C)) := rfl
  simp [this]; rfl

@[simp] lemma coe_sSup {U : Set (RegularOpens X)} :
    ((sSup U : RegularOpens X) : Set X) =
    interior (closure (⋃₀ ((fun u : RegularOpens X ↦ closure u) '' U))) := by
  have : sSup U = (sSup (cl '' U)).int := rfl
  simp [this]

-- ??? do we have `sSup = int(cl ∪ U_i)`???


--example (A B : Set X) : interior A ∩ interior B = interior (A ∩ B) := by exact interior_inter.symm

-- example (A B : Set X) : closure A ∪ closure B = closure (A ∪ B) := closure_union.symm

example (A B : Set X) (h : IsOpen A) : A ∩ closure B ⊆ closure (A ∩ B) := by exact IsOpen.inter_closure h

example (τ : Type*) (A B : Set τ) [CompleteLattice τ](S : Set τ) : ⨆ V ∈ S, V = sSup S := by exact sSup_eq_iSup.symm


lemma temp_lemma (U : RegularOpens X) (S : Set (RegularOpens X)) : ⨆ V ∈ S, U ⊓ V = sSup ((fun V ↦ U ⊓ V)'' S) := by sorry

example (A : Set X) (S : Set (RegularOpens X)) : ⨆ V ∈ S, V = sSup S:= by exact sSup_eq_iSup.symm

example [Nonempty X] (a : X) : (range fun (x : X) ↦ a) = {a} := by simp

example (U : Set X) (h : IsOpen U) : U = interior U := by exact (IsOpen.interior_eq h).symm

example {Z : Type*} (a : Set Z) (f : ℕ → Set Z): a ∩ (⋃ i , f i) = ⋃ i, a ∩ f i := by exact inter_iUnion a fun i ↦ f i

#check inter_iUnion₂
#check iUnion

example {Z : Type*} (a : Set Z) (C : Set (Set Z)) (f : Set Z → Set Z): a ∩ ⋃ c ∈ C, f c = ⋃ c ∈ C, a ∩ f c := by exact inter_iUnion₂ a fun i j ↦ f i

example {Z W: Type*} (f g : W → Set Z) (H : ∀ w, f w ⊆ g w) : ⋃ w, f w ⊆  ⋃ w, g w := by exact iUnion_mono H

lemma inf_sSup_le_iSup_inf_RegularOpens (U : RegularOpens X) (S : Set (RegularOpens X)) : U ⊓ sSup S ≤ ⨆ V ∈ S, U ⊓ V := by
  have h1 : (U : Set X) ∩ interior (closure (⋃ V ∈ S, closure V)) = U ⊓ sSup S:= by simp

  have h2 : interior (closure (⋃ V ∈ S, closure ((U : Set X) ∩ V))) = sSup {U ⊓ V | V ∈ S} := by
    simp

  have h3 : sSup {U ⊓ V | V ∈ S} = ⨆ V ∈ S, U ⊓ V := by
    rw [← sSup_image]
    ext W
    simp

  have h4 : (U : Set X) ∩ interior (closure (⋃ V ∈ S, closure V)) ⊆ interior (closure (⋃ V ∈ S, closure (U ∩ V))) := by
    calc (U : Set X) ∩ interior (closure (⋃ V ∈ S, closure V)) = U.1 ∩ interior (closure (⋃ V ∈ S, closure V)) := by simp
    _ = interior U.1 ∩ interior (closure (⋃ V ∈ S, closure V)) := by rw [IsOpen.interior_eq U.2]
    _ = interior (U.1 ∩ closure (⋃ V ∈ S, closure V)) := interior_inter.symm
    _ ⊆ interior (closure (U.1 ∩ (⋃ V ∈ S, closure V))) := interior_mono (IsOpen.inter_closure U.2)
    _ = interior (closure (⋃ V ∈ S, U.1 ∩ closure V)) := by
      have : U.1 ∩ (⋃ V ∈ S, closure V) = ⋃ V ∈ S, U.1 ∩ closure V := by
        ext x
        simp
      rw [this]
    _ ⊆ interior (closure (⋃ V ∈ S, closure (U.1 ∩ V))) := by
      apply interior_mono
      apply closure_mono
      intro V
      simp
      intro hV x hx hVx
      use x
      exact ⟨hx, IsOpen.inter_closure U.2 ⟨hV, hVx⟩⟩
    _ = interior (closure (⋃ V ∈ S, closure (U ∩ V))) := by simp

  rw [le_def, ← h1, ← h3, ← h2]
  exact h4

lemma iInf_sup_le_sup_sInf_RegularOpens (U : RegularOpens X) (S : Set (RegularOpens X)) : ⨅ V ∈ S, U ⊔ V ≤ U ⊔ sInf S := by
  have aux : ⨅ V ∈ S, U ⊔ V = sInf {U ⊔ V | V ∈ S} := by
    rw [← sInf_image]
    ext
    simp



  rw [le_def]
  simp
  sorry
  -- intro x hx




/- We still have to prove that this gives a distributive lattice.
Note: these are hard; you might want to do the next exercises first. -/
instance completeDistribLattice : CompleteDistribLattice (RegularOpens X) :=
  { completeLattice with
    inf_sSup_le_iSup_inf := inf_sSup_le_iSup_inf_RegularOpens
    iInf_sup_le_sup_sInf := iInf_sup_le_sup_sInf_RegularOpens
}

/-
instance : HasCompl (RegularOpens X) := {
  compl := fun U => ⟨interior (U.1)ᶜ, isOpen_interior, int_cl_int_eq_int (isClosed_compl_iff.mpr U.2)⟩
}

example (A : Set X) (h : IsOpen A) : IsClosed Aᶜ := by exact isClosed_compl_iff.mpr h

-- instance : HasCompl (RegularOpens X) where
--  compl U := U

@[simp]
lemma coe_compl (U : RegularOpens X) : ↑Uᶜ = interior (U : Set X)ᶜ := by rfl
-- ahhh???

-- example (C : Set X) : C ∩ Cᶜ = ∅ := by exact inter_compl_self C
example (C : Set X) : C ∪ Cᶜ = univ := by exact union_compl_self C

example (U: Set X) (h: univ ⊆ U): U = univ := by exact univ_subset_iff.mp h

example (C D E: Set X) (h: C ⊆ D): C ∪ E ⊆ D ∪ E := by exact union_subset_union_left E h


lemma myLemma {U: Set X} : interior (closure U ∪ Uᶜ) = univ := by
  rw [univ_subset_iff.symm]
  calc univ = interior univ := interior_univ.symm
  _ = interior (U ∪ Uᶜ) := by rw [union_compl_self U]
  _ ⊆ interior (closure U ∪ Uᶜ) := interior_mono (union_subset_union_left (Uᶜ) subset_closure)


instance : CompleteBooleanAlgebra (RegularOpens X) :=
  { completeDistribLattice,
    inferInstanceAs (DistribLattice (RegularOpens X)) with
    inf_compl_le_bot := by
      intro U
      simp
      ext x
      simp
      exact fun h => subset_closure h
    top_le_sup_compl := by
      intro U
      simp
      ext x
      simp
      have : x ∈ interior (closure U.1 ∪ (U.1)ᶜ) -- emmm rw does not work without surprise, need to do this (flip the proof???)
      . rw [myLemma]
        trivial
      simp at this
      exact this
  }
-/
