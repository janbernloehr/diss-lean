import NLS.FunctionalAnalysis.SpectralPeakFunction
import NLS.FunctionalAnalysis.NormalOperatorSpectralMeasure
import NLS.FunctionalAnalysis.VectorSpectralMeasureAtomBound

/-! # Actual normal-operator estimates for spectral peak functions -/
noncomputable section
set_option autoImplicit false
open MeasureTheory
namespace NLS.FunctionalAnalysis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The actual CFC of a spectral peak is contractive. -/
theorem norm_cfc_spectralPeak_apply_le (U : E →L[ℂ] E) (hU : IsStarNormal U)
    (a : ℂ) (ε : ℝ) (hε : 0 < ε) (v : E) :
    ‖cfcHom hU (spectralPeakFunction (spectrum ℂ U) a ε hε) v‖ ≤ ‖v‖ := by
  have h := norm_spectralPeakFunction_le_one (spectrum ℂ U) a ε hε
  rw [← norm_cfcHom U _ hU] at h
  exact (ContinuousLinearMap.le_opNorm _ v).trans
    ((mul_le_mul_of_nonneg_right h (norm_nonneg v)).trans_eq (one_mul _))

/-- Applying the peak to the range of the original operator pencil is small. -/
theorem norm_cfc_spectralPeak_pencil_apply_le (U : E →L[ℂ] E) (hU : IsStarNormal U)
    (a : ℂ) (ε : ℝ) (hε : 0 < ε) (w : E) :
    ‖cfcHom hU (spectralPeakFunction (spectrum ℂ U) a ε hε)
      ((U-a • (1 : E →L[ℂ] E)) w)‖ ≤ ε*‖w‖ := by
  let f := spectralPeakFunction (spectrum ℂ U) a ε hε
  let coord : C(spectrum ℂ U, ℂ) := ContinuousMap.restrict (spectrum ℂ U) (ContinuousMap.id ℂ)
  let q := f*(coord-a • (1 : C(spectrum ℂ U, ℂ)))
  have hq : cfcHom hU q = (cfcHom hU f)*(U-a • (1 : E →L[ℂ] E)) := by
    dsimp only [q]
    rw [map_mul,map_sub,map_smul,map_one]
    change _*(cfcHom hU (ContinuousMap.restrict (spectrum ℂ U) (ContinuousMap.id ℂ))-_) = _
    rw [cfcHom_id]
  have hn : ‖q‖ ≤ ε := by
    apply (ContinuousMap.norm_le _ hε.le).mpr
    intro x
    change ‖spectralPeakFunction (spectrum ℂ U) a ε hε x*((x : ℂ)-a*1)‖ ≤ ε
    simpa only [mul_one] using norm_spectralPeakFunction_mul_sub_le (spectrum ℂ U) a ε hε x
  have hop : ‖cfcHom hU q‖ ≤ ε := by rw [norm_cfcHom U q hU]; exact hn
  have he : cfcHom hU q w = cfcHom hU f ((U-a • (1 : E →L[ℂ] E)) w) :=
    congrArg (fun A : E →L[ℂ] E => A w) hq
  rw [← he]
  exact (ContinuousLinearMap.le_opNorm _ w).trans
    (mul_le_mul_of_nonneg_right hop (norm_nonneg w))

/-- The scalar spectral atom is controlled by approximation from the actual pencil range. -/
theorem normalOperatorSpectralMeasure_atom_le_pencil_approx
    (U : E →L[ℂ] E) (hU : IsStarNormal U) (v : E) (a : spectrum ℂ U)
    (ε : ℝ) (hε : 0 < ε) (w : E) :
    (normalOperatorSpectralMeasure U hU v).real {a} ≤
      (‖v-(U-(a : ℂ) • (1 : E →L[ℂ] E)) w‖+ε*‖w‖)^2 := by
  let f := spectralPeakFunction (spectrum ℂ U) a ε hε
  let A := U-(a : ℂ) • (1 : E →L[ℂ] E)
  have ha : (normalOperatorSpectralMeasure U hU v).real {a} ≤ ‖cfcHom hU f v‖^2 :=
    vectorSpectralMeasure_atom_le_norm_apply_sq (cfcHom hU) v a f
      (spectralPeakFunction_self (spectrum ℂ U) a ε hε)
  have hsplit : cfcHom hU f v = cfcHom hU f (v-A w)+cfcHom hU f (A w) := by
    rw [← map_add,sub_add_cancel]
  have hb : ‖cfcHom hU f v‖ ≤ ‖v-A w‖+ε*‖w‖ := by
    rw [hsplit]
    exact (norm_add_le _ _).trans (add_le_add
      (norm_cfc_spectralPeak_apply_le U hU a ε hε (v-A w))
      (norm_cfc_spectralPeak_pencil_apply_le U hU a ε hε w))
  exact ha.trans (pow_le_pow_left₀ (norm_nonneg _) hb 2)

end NLS.FunctionalAnalysis
