import NLS.FunctionalAnalysis.NormalOperatorPencilDense
import NLS.FunctionalAnalysis.NormalSpectralPeakEstimates

/-! # Absence of atoms for actual normal-operator scalar spectral measures -/
noncomputable section
set_option autoImplicit false
open MeasureTheory
namespace NLS.FunctionalAnalysis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Dense range of the actual pencil excludes the corresponding spectral atom. -/
theorem normalOperatorSpectralMeasure_singleton_eq_zero_of_denseRange
    (U : E →L[ℂ] E) (hU : IsStarNormal U) (v : E) (a : spectrum ℂ U)
    (hd : DenseRange (U-(a : ℂ) • (1 : E →L[ℂ] E))) :
    normalOperatorSpectralMeasure U hU v {a} = 0 := by
  apply (measureReal_eq_zero_iff).mp
  apply le_antisymm _ measureReal_nonneg
  by_contra hzero
  have hm : 0 < (normalOperatorSpectralMeasure U hU v).real {a} := lt_of_not_ge hzero
  let δ := Real.sqrt ((normalOperatorSpectralMeasure U hU v).real {a})
  have hδ : 0 < δ := Real.sqrt_pos.mpr hm
  have hδsq : δ^2 = (normalOperatorSpectralMeasure U hU v).real {a} := Real.sq_sqrt hm.le
  obtain ⟨w,hw⟩ := Metric.denseRange_iff.mp hd v (δ/2) (by positivity)
  rw [dist_eq_norm] at hw
  let ε := δ/(2*(‖w‖+1))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hew : ε*‖w‖ < δ/2 := by
    dsimp only [ε]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ (by positivity : 0 < 2*(‖w‖+1))).mpr
    nlinarith
  have hb := normalOperatorSpectralMeasure_atom_le_pencil_approx U hU v a ε hε w
  have hs : ‖v-(U-(a : ℂ) • (1 : E →L[ℂ] E)) w‖+ε*‖w‖ < δ := by linarith
  have hn : 0 ≤ ‖v-(U-(a : ℂ) • (1 : E →L[ℂ] E)) w‖+ε*‖w‖ := by positivity
  nlinarith

/-- The scalar CFC measures of a bounded normal operator with no eigenvectors
have no atoms. This is a theorem about the constructed measures themselves. -/
theorem normalOperatorSpectralMeasure_noAtoms (U : E →L[ℂ] E) (hU : IsStarNormal U)
    (hno : ∀ (ζ : ℂ) (v : E), U v = ζ • v → v = 0) (v : E) :
    NullSingletonClass (normalOperatorSpectralMeasure U hU v) := by
  constructor
  intro a
  exact normalOperatorSpectralMeasure_singleton_eq_zero_of_denseRange U hU v a
    (denseRange_boundedOperatorPencil_of_no_eigenvectors U hU hno a)

end NLS.FunctionalAnalysis
