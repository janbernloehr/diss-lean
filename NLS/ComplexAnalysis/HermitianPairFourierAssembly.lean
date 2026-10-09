import NLS.ComplexAnalysis.HermitianFourierAssembly

/-! # Actual vector Fourier coefficients in the Hermitian pair norm -/
noncomputable section
open MeasureTheory NLS.Fourier
open scoped ENNReal
namespace NLS.ComplexAnalysis

abbrev HermitianPairCoeff (q : ℝ≥0∞) := lp (fun _ : ℤ => HermitianPair) q

/-- Evaluation on the first Hermitian unit vector extracts the first matrix column. -/
def hermitianFirstColumnCLM : HermitianOperator →L[ℂ] HermitianPair :=
  ContinuousLinearMap.apply ℂ HermitianPair (hermitianPair (1,0))

@[simp] theorem hermitianFirstColumnCLM_columns (u v : ℂ × ℂ) :
    hermitianFirstColumnCLM (hermitianColumns u v) = hermitianPair u := by
  change hermitianColumns u v (hermitianPair (1,0)) = _
  simp

theorem norm_hermitianFirstColumnCLM_le : ‖hermitianFirstColumnCLM‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro A
  have h := A.le_opNorm (hermitianPair (1,0))
  simpa [hermitianPair_norm,hermitianFirstColumnCLM] using h

def hermitianFirstColumnCoefficients {q : ℝ≥0∞} [Fact (1 ≤ q)] :
    HermitianCoeff q →L[ℂ] HermitianPairCoeff q :=
  lp.mapCLM q (fun _ : ℤ => hermitianFirstColumnCLM) zero_le_one
    (fun _ => norm_hermitianFirstColumnCLM_le)

def hermitianPairFourierAssembly {q : ℝ≥0∞} [Fact (1 ≤ q)] (a b : Coeff q) :
    HermitianPairCoeff q := hermitianFirstColumnCoefficients (hermitianFourierAssembly a b 0 0)

@[simp] theorem hermitianPairFourierAssembly_apply {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (a b : Coeff q) (k : ℤ) : hermitianPairFourierAssembly a b k = hermitianPair (a k,b k) := by
  change hermitianFirstColumnCLM (hermitianFourierAssembly a b 0 0 k) = _
  rw [hermitianFourierAssembly_apply,hermitianFirstColumnCLM_columns]

theorem norm_hermitianPairFourierAssembly_le {q : ℝ≥0∞} [Fact (1 ≤ q)] (a b : Coeff q) :
    ‖hermitianPairFourierAssembly a b‖ ≤ ‖a‖+‖b‖ := by
  have h : ‖(hermitianFirstColumnCoefficients : HermitianCoeff q →L[ℂ] HermitianPairCoeff q)‖ ≤ 1 :=
    lp.norm_mapCLM_le _ _ _ _
  apply ((hermitianFirstColumnCoefficients).le_of_opNorm_le h _).trans
  simpa using norm_hermitianFourierAssembly_le a b 0 0

/-- The assembled coefficients are the actual vector-valued Bochner Fourier integrals. -/
theorem hermitianPair_intervalFourierCoefficient (f g : ℝ → ℂ)
    (hf : Continuous f) (hg : Continuous g) (k : ℤ) :
    hermitianPair (intervalFourierCoefficient 1 f k,intervalFourierCoefficient 1 g k) =
      ∫ t in (0 : ℝ)..1, wave (-k) (2*t) • hermitianPair (f t,g t) := by
  have h := congrArg hermitianFirstColumnCLM
    (hermitianColumns_intervalFourierCoefficient (fun t => (f t,g t)) (fun _ => 0)
      (hf.prodMk hg) continuous_const k)
  have hw : Continuous (fun t : ℝ => wave (-k) (2*t)) :=
    (continuous_wave _).comp (continuous_const.mul continuous_id)
  have hz : Continuous (fun _ : ℝ => (0 : ℂ × ℂ)) := continuous_const
  have hc : Continuous (fun t => hermitianColumns (f t,g t) 0) := by
    simpa only [Function.comp_def] using continuous_hermitianColumns.comp ((hf.prodMk hg).prodMk hz)
  have hi : IntervalIntegrable (fun t => wave (-k) (2*t) • hermitianColumns (f t,g t) 0) volume 0 1 :=
    (hw.smul hc).intervalIntegrable 0 1
  rw [← hermitianFirstColumnCLM.intervalIntegral_comp_comm hi] at h
  simpa only [map_smul,hermitianFirstColumnCLM_columns] using h

end NLS.ComplexAnalysis
