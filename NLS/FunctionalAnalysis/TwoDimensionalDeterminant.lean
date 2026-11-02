import NLS.FunctionalAnalysis.FiniteSpectralDeterminant
import Mathlib.LinearAlgebra.Basis.Fin

/-! # Determinants and quantitative shifts on a two-dimensional product -/

noncomputable section
namespace NLS.FiniteSpectralDeterminant
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

theorem det_prod_formula (T : (𝕜 × 𝕜) →L[𝕜] (𝕜 × 𝕜)) :
    T.toLinearMap.det = (T (1,0)).1*(T (0,1)).2 - (T (0,1)).1*(T (1,0)).2 := by
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd 𝕜), Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, Module.Basis.coe_finTwoProd_repr]

theorem determinant_shift_bound (E : (𝕜 × 𝕜) →L[𝕜] (𝕜 × 𝕜))
    (a : 𝕜) (C : ℝ) (hC : 0 ≤ C)
    (h1 : ‖E (1,0)‖ ≤ C) (h2 : ‖E (0,1)‖ ≤ C) :
    ‖(a • ContinuousLinearMap.id 𝕜 (𝕜 × 𝕜)-E).toLinearMap.det - a^2‖ ≤
      2*‖a‖*C+2*C^2 := by
  have h11 := (norm_fst_le (E (1,0))).trans h1
  have h21 := (norm_snd_le (E (1,0))).trans h1
  have h12 := (norm_fst_le (E (0,1))).trans h2
  have h22 := (norm_snd_le (E (0,1))).trans h2
  have he : (a • ContinuousLinearMap.id 𝕜 (𝕜 × 𝕜)-E).toLinearMap.det - a^2 =
      -a*(E (1,0)).1 - a*(E (0,1)).2 +
        (E (1,0)).1*(E (0,1)).2 - (E (0,1)).1*(E (1,0)).2 := by
    rw [det_prod_formula]
    change (a*1-(E (1,0)).1)*(a*1-(E (0,1)).2) -
      (a*0-(E (0,1)).1)*(a*0-(E (1,0)).2) - a^2 = _
    ring
  rw [he]
  calc
    _ ≤ ‖-a*(E (1,0)).1 - a*(E (0,1)).2 + (E (1,0)).1*(E (0,1)).2‖ +
        ‖(E (0,1)).1*(E (1,0)).2‖ := norm_sub_le _ _
    _ ≤ (‖-a*(E (1,0)).1 - a*(E (0,1)).2‖ +
        ‖(E (1,0)).1*(E (0,1)).2‖) + ‖(E (0,1)).1*(E (1,0)).2‖ :=
      add_le_add (norm_add_le _ _) le_rfl
    _ ≤ ((‖-a*(E (1,0)).1‖ + ‖a*(E (0,1)).2‖) +
        ‖(E (1,0)).1*(E (0,1)).2‖) + ‖(E (0,1)).1*(E (1,0)).2‖ :=
      add_le_add (add_le_add (norm_sub_le _ _) le_rfl) le_rfl
    _ = ‖a‖*‖(E (1,0)).1‖ + ‖a‖*‖(E (0,1)).2‖ +
        ‖(E (1,0)).1‖*‖(E (0,1)).2‖ + ‖(E (0,1)).1‖*‖(E (1,0)).2‖ := by
      simp only [norm_mul, norm_neg]
    _ ≤ ‖a‖*C+‖a‖*C+C*C+C*C := by gcongr
    _ = _ := by ring

end NLS.FiniteSpectralDeterminant
