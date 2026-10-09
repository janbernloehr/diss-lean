import NLS.ComplexAnalysis.HermitianPair
import NLS.Fourier.IntervalCoefficientScaling
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Tactic.FinCases

/-! # Assembling actual Fourier coefficients in the Hermitian operator norm -/
noncomputable section
open MeasureTheory NLS.Fourier
open scoped ENNReal
namespace NLS.ComplexAnalysis

abbrev HermitianOperator := HermitianPair →L[ℂ] HermitianPair
abbrev HermitianCoeff (q : ℝ≥0∞) := lp (fun _ : ℤ => HermitianOperator) q

/-- The four coordinate matrix units act on Euclidean vectors. -/
def hermitianMatrixUnit (i j : Fin 2) : HermitianOperator :=
  hermitianColumns (if j = 0 then (if i = 0 then (1,0) else (0,1)) else 0)
    (if j = 1 then (if i = 0 then (1,0) else (0,1)) else 0)

theorem norm_hermitianMatrixUnit_le (i j : Fin 2) : ‖hermitianMatrixUnit i j‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro w
  obtain ⟨v,rfl⟩ := hermitianPairEquiv.symm.surjective w
  change ‖hermitianMatrixUnit i j (hermitianPair v)‖ ≤ 1*‖hermitianPair v‖
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  fin_cases i <;> fin_cases j <;>
    simp [hermitianMatrixUnit,hermitianColumns_apply,hermitianPair_norm,
      Prod.smul_mk,smul_eq_mul]
  all_goals rw [Real.sq_sqrt (by positivity)]; nlinarith [sq_nonneg ‖v.1‖,sq_nonneg ‖v.2‖]

/-- Entry decomposition, in column order. -/
theorem hermitianColumns_eq_matrixUnits (u v : ℂ × ℂ) :
    hermitianColumns u v =
      u.1 • hermitianMatrixUnit 0 0 + u.2 • hermitianMatrixUnit 1 0 +
      v.1 • hermitianMatrixUnit 0 1 + v.2 • hermitianMatrixUnit 1 1 := by
  ext w
  obtain ⟨x,rfl⟩ := hermitianPairEquiv.symm.surjective w
  apply hermitianPairEquiv.injective
  simp [hermitianMatrixUnit,hermitianColumns,smul_eq_mul,mul_comm]
  ext <;> simp [smul_eq_mul,mul_comm]

/-- Lift scalar coefficients through a single matrix unit. -/
def hermitianEntryCoefficients {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (i j : Fin 2) : Coeff q →L[ℂ] HermitianCoeff q :=
  lp.mapCLM q (fun _ : ℤ => (ContinuousLinearMap.id ℂ ℂ).smulRight (hermitianMatrixUnit i j))
    zero_le_one (fun _ => by
      simpa only [ContinuousLinearMap.norm_smulRight_apply,ContinuousLinearMap.norm_id,one_mul]
        using norm_hermitianMatrixUnit_le i j)

@[simp] theorem hermitianEntryCoefficients_apply {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (i j : Fin 2) (a : Coeff q) (k : ℤ) :
    hermitianEntryCoefficients i j a k = a k • hermitianMatrixUnit i j := rfl

theorem norm_hermitianEntryCoefficients_le {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (i j : Fin 2) (a : Coeff q) : ‖hermitianEntryCoefficients i j a‖ ≤ ‖a‖ := by
  apply (hermitianEntryCoefficients i j).le_of_opNorm_le _ a |>.trans_eq (one_mul _)
  exact lp.norm_mapCLM_le _ _ _ _

/-- The full operator-valued sequence, with the genuine induced norm at each frequency. -/
def hermitianFourierAssembly {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (a b c d : Coeff q) : HermitianCoeff q :=
  hermitianEntryCoefficients 0 0 a + hermitianEntryCoefficients 1 0 b +
    hermitianEntryCoefficients 0 1 c + hermitianEntryCoefficients 1 1 d

@[simp] theorem hermitianFourierAssembly_apply {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (a b c d : Coeff q) (k : ℤ) :
    hermitianFourierAssembly a b c d k = hermitianColumns (a k,b k) (c k,d k) := by
  simp [hermitianFourierAssembly,hermitianColumns_eq_matrixUnits]

theorem norm_hermitianFourierAssembly_le {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (a b c d : Coeff q) :
    ‖hermitianFourierAssembly a b c d‖ ≤ ‖a‖+‖b‖+‖c‖+‖d‖ := by
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add
        (norm_hermitianEntryCoefficients_le _ _ _) (norm_hermitianEntryCoefficients_le _ _ _)))
      (norm_hermitianEntryCoefficients_le _ _ _))) (norm_hermitianEntryCoefficients_le _ _ _))

/-- Assembly commutes with the actual unit-interval Bochner Fourier integral. -/
theorem hermitianColumns_intervalFourierCoefficient (u v : ℝ → ℂ × ℂ)
    (hu : Continuous u) (hv : Continuous v) (k : ℤ) :
    hermitianColumns
      (intervalFourierCoefficient 1 (fun t => (u t).1) k,
       intervalFourierCoefficient 1 (fun t => (u t).2) k)
      (intervalFourierCoefficient 1 (fun t => (v t).1) k,
       intervalFourierCoefficient 1 (fun t => (v t).2) k) =
    ∫ t in (0 : ℝ)..1, wave (-k) (2*t) • hermitianColumns (u t) (v t) := by
  have hc (f : ℝ → ℂ) (hf : Continuous f) (i j : Fin 2) :
      IntervalIntegrable (fun t => (f t * wave (-k) (2*t)) • hermitianMatrixUnit i j)
        volume 0 1 :=
    ((hf.mul ((continuous_wave (-k)).comp (continuous_const.mul continuous_id))).smul
      continuous_const).intervalIntegrable _ _
  simp only [hermitianColumns_eq_matrixUnits,smul_add,smul_smul]
  simp_rw [mul_comm (wave (-k) (2 * _))]
  rw [intervalIntegral.integral_add ((hc _ hu.fst 0 0).add (hc _ hu.snd 1 0) |>.add
      (hc _ hv.fst 0 1)) (hc _ hv.snd 1 1),
    intervalIntegral.integral_add ((hc _ hu.fst 0 0).add (hc _ hu.snd 1 0)) (hc _ hv.fst 0 1),
    intervalIntegral.integral_add (hc _ hu.fst 0 0) (hc _ hu.snd 1 0)]
  simp [intervalFourierCoefficient]

end NLS.ComplexAnalysis
