import Mathlib.Algebra.Exact
import Mathlib.CategoryTheory.Iso
import Mathlib.Algebra.Category.ModuleCat.Basic

-- Record some results on exactness
open Function LinearMap CategoryTheory

section
universe u v
variable {R : Type u} [Ring R]
variable {M N P : Type v} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [Module R M] [Module R N] [Module R P]
variable {f : M →ₗ[R] N} {g : N →ₗ[R] P}
variable (e : Exact f g)

lemma exact_iso_of_range_eq_bot [IsIso (ModuleCat.ofHom g)] : range (f) = ⊥ := by
  rw [← Exact.linearMap_ker_eq e]
  apply LinearEquiv.ker (Iso.toLinearEquiv (asIso (ModuleCat.ofHom (g))))


lemma iso_exact_of_ker_eq_top [IsIso (ModuleCat.ofHom (f))] : ker g = ⊤ := by
  rw [Exact.linearMap_ker_eq e]
  apply LinearEquiv.range (Iso.toLinearEquiv (asIso (ModuleCat.ofHom f)))

lemma exact_iso_of_fst_eq_zero [IsIso (ModuleCat.ofHom g)] : f = 0 :=
  range_eq_bot.mp <| exact_iso_of_range_eq_bot e

lemma iso_exact_of_snd_eq_zero [IsIso (ModuleCat.ofHom f)] : g = 0 :=
  ker_eq_top.mp <| iso_exact_of_ker_eq_top e

end

section
universe u v
variable {R : Type u} [Ring R]
variable {M₀ M₁ M₂ M₃ M₄ : Type v}
variable [AddCommGroup M₀] [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃] [AddCommGroup M₄]
variable [Module R M₀] [Module R M₁] [Module R M₂] [Module R M₃] [Module R M₄]
variable {f₀ : M₀ →ₗ[R] M₁} {f₁ : M₁ →ₗ[R] M₂} {f₂ : M₂ →ₗ[R] M₃} {f₃ : M₃ →ₗ[R] M₄}
variable (e₁ : Exact f₀ f₁) (e₂ : Exact f₁ f₂) (e₃ : Exact f₂ f₃)

lemma exact_iso_iso_of_subsingleton (h₁ : IsIso (ModuleCat.ofHom f₀)) (h₂ : IsIso (ModuleCat.ofHom f₃)) : Subsingleton M₂ := by
  have h1 : f₂ = 0 := exact_iso_of_fst_eq_zero e₃
  have h2 : f₁ = 0 := iso_exact_of_snd_eq_zero e₁
  have h3 : ker f₂ = range f₁ := Exact.linearMap_ker_eq e₂
  -- have h3 : (ker (f 2) : Set (M 2)) = range (f 1) := by rw [h3]
  rw [ker_eq_top.mpr h1, range_eq_bot.mpr h2] at h3
  have : Subsingleton <| Submodule R M₂ := subsingleton_iff_bot_eq_top.mp h3.symm
  apply subsingleton_of_forall_eq 0
  intro y
  have : y ∈ (⊤ : Submodule R M₂) := trivial
  rw [h3] at this
  exact this
end

/-
-- casts between `Fin` raise so much trouble
section
variable {R : Type*} [Ring R]
variable {M : Fin 4 → Type} [(i : Fin 4) → AddCommGroup (M i)] [(i : Fin 4) → Module R (M i)]
variable {f : (i : Fin 3) → (M i) →ₗ[R] (M (i+1))}
variable (e₁ : Exact (f 0) (f 1)) (e₂ : Exact (f 1) (f 2))

lemma short_exact_subsingleton_subsingleton_of_iso [Subsingleton (M 0)] [ Subsingleton (M 3)]: (M 1) ≃ₗ[R] (M 2) := by
  apply LinearEquiv.ofBijective (f 1)
  dsimp [Bijective]
  constructor
  . apply LinearMap.ker_eq_bot.mp
    rw [Exact.linearMap_ker_eq <| e₁]
    apply LinearMap.range_eq_bot.mpr
    have : Subsingleton (M (0 : Fin 3)) := by simp; infer_instance

  . apply LinearMap.range_eq_top.mp
    rw [← Exact.linearMap_ker_eq <| e₂]
    apply LinearMap.ker_eq_top.mpr
    simp only [Fin.val_one, Fin.val_two, Nat.cast_ofNat]


end
-/
section
universe u v
variable {R : Type u} [Ring R]
variable {M₀ M₁ M₂ M₃ : Type v}
variable [AddCommGroup M₀] [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
variable [Module R M₀] [Module R M₁] [Module R M₂] [Module R M₃]
variable {f₀ : M₀ →ₗ[R] M₁} {f₁ : M₁ →ₗ[R] M₂} {f₂ : M₂ →ₗ[R] M₃}
variable (e₁ : Exact f₀ f₁) (e₂ : Exact f₁ f₂)


lemma exact_subsingleton_subsingleton_of_bijective [Subsingleton M₀] [Subsingleton M₃]: Bijective f₁ := by
  dsimp [Bijective]
  constructor
  . apply LinearMap.ker_eq_bot.mp
    rw [Exact.linearMap_ker_eq <| e₁]
    apply LinearMap.range_eq_bot.mpr
    simp only [eq_iff_true_of_subsingleton]
  . apply LinearMap.range_eq_top.mp
    rw [← Exact.linearMap_ker_eq <| e₂]
    apply LinearMap.ker_eq_top.mpr
    simp only [eq_iff_true_of_subsingleton]

example (h : Bijective f₁) : (LinearEquiv.ofBijective f₁ h) = f₁ := rfl

noncomputable def exact_subsingleton_subsingleton_of_linear_equiv [Subsingleton M₀] [Subsingleton M₃]: M₁ ≃ₗ[R] M₂ := LinearEquiv.ofBijective f₁ <| exact_subsingleton_subsingleton_of_bijective e₁ e₂

lemma exact_subsingleton_subsingleton_of_isiso (h₁ : Subsingleton M₀) (h₂ : Subsingleton M₃): IsIso (ModuleCat.ofHom f₁) := by
  have : (LinearEquiv.ofBijective f₁ (exact_subsingleton_subsingleton_of_bijective e₁ e₂)) = f₁ := rfl
  set h := (LinearEquiv.ofBijective f₁ (exact_subsingleton_subsingleton_of_bijective e₁ e₂))
  set h' := LinearEquiv.toModuleIso h
  have : ModuleCat.ofHom f₁ = h'.hom := rfl
  rw [this]
  exact ⟨h'.inv, ⟨h'.hom_inv_id, h'.inv_hom_id⟩⟩

end
