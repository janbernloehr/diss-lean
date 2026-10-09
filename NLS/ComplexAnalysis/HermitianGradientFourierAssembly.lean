import NLS.ComplexAnalysis.HermitianFourierAssembly
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-! # Full matrix gradients in the induced Hermitian operator norm

A gradient is a linear map from the two potential components to a matrix
acting on Hermitian vectors. All Fourier coefficients use this induced
operator norm, including the direction variable.
-/
noncomputable section
open MeasureTheory NLS.Fourier
open scoped ENNReal
namespace NLS.ComplexAnalysis

-- Cache the standard normed structures for the nested operator spaces.
local instance : NormedAddCommGroup HermitianOperator := inferInstance
local instance : NormedSpace ℂ HermitianOperator := inferInstance

abbrev HermitianGradient := HermitianPair →L[ℂ] HermitianOperator
local instance : NormedAddCommGroup HermitianGradient := inferInstance
local instance : NormedSpace ℂ HermitianGradient := inferInstance

abbrev HermitianGradientCoeff (q : ℝ≥0∞) := lp (fun _ : ℤ => HermitianGradient) q

def hermitianCoordinate (i : Fin 2) : HermitianPair →L[ℂ] ℂ :=
  (if i = 0 then ContinuousLinearMap.fst ℂ ℂ ℂ else ContinuousLinearMap.snd ℂ ℂ ℂ).comp
    hermitianPairEquiv.toContinuousLinearMap

theorem norm_hermitianCoordinate_le (i : Fin 2) : ‖hermitianCoordinate i‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro w
  obtain ⟨v,rfl⟩ := hermitianPairEquiv.symm.surjective w
  change ‖hermitianCoordinate i (hermitianPair v)‖ ≤ 1*‖hermitianPair v‖
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  fin_cases i <;> simp [hermitianCoordinate,hermitianPair,hermitianPairEquiv,
    WithLp.prod_norm_sq_eq_of_L2]

/-- Insert a matrix in one potential component. -/
def hermitianGradientLift (i : Fin 2) : HermitianOperator →L[ℂ] HermitianGradient :=
  ContinuousLinearMap.smulRightL ℂ HermitianPair HermitianOperator (hermitianCoordinate i)

theorem norm_hermitianGradientLift_le (i : Fin 2) : ‖hermitianGradientLift i‖ ≤ 1 := by
  rw [hermitianGradientLift,ContinuousLinearMap.norm_smulRightL]
  exact norm_hermitianCoordinate_le i

def hermitianGradientColumns (A B : HermitianOperator) : HermitianGradient :=
  hermitianGradientLift 0 A + hermitianGradientLift 1 B

@[simp] theorem hermitianGradientColumns_apply (A B : HermitianOperator) (h : ℂ × ℂ) :
    hermitianGradientColumns A B (hermitianPair h) = h.1 • A + h.2 • B := by
  simp [hermitianGradientColumns,hermitianGradientLift,hermitianCoordinate,hermitianPair]

def hermitianGradientLiftCoefficients {q : ℝ≥0∞} [Fact (1 ≤ q)] (i : Fin 2) :
    HermitianCoeff q →L[ℂ] HermitianGradientCoeff q :=
  lp.mapCLM q (fun _ : ℤ => hermitianGradientLift i) zero_le_one
    (fun _ => norm_hermitianGradientLift_le i)

theorem norm_hermitianGradientLiftCoefficients_le {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (i : Fin 2) (a : HermitianCoeff q) : ‖hermitianGradientLiftCoefficients i a‖ ≤ ‖a‖ := by
  apply (hermitianGradientLiftCoefficients i).le_of_opNorm_le _ a |>.trans_eq (one_mul _)
  exact lp.norm_mapCLM_le _ _ _ _

/-- Assemble both matrix-valued gradient components, preserving their Fourier frequencies. -/
def hermitianGradientFourierAssembly {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (a b : HermitianCoeff q) : HermitianGradientCoeff q :=
  hermitianGradientLiftCoefficients 0 a + hermitianGradientLiftCoefficients 1 b

@[simp] theorem hermitianGradientFourierAssembly_apply {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (a b : HermitianCoeff q) (k : ℤ) :
    hermitianGradientFourierAssembly a b k = hermitianGradientColumns (a k) (b k) := rfl

theorem norm_hermitianGradientFourierAssembly_le {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (a b : HermitianCoeff q) : ‖hermitianGradientFourierAssembly a b‖ ≤ ‖a‖+‖b‖ :=
  (norm_add_le _ _).trans (add_le_add (norm_hermitianGradientLiftCoefficients_le 0 a)
    (norm_hermitianGradientLiftCoefficients_le 1 b))

/-- Assembly commutes with the actual gradient-valued Bochner Fourier integral. -/
theorem hermitianGradientColumns_intervalIntegral (A B : ℝ → HermitianOperator)
    (hA : Continuous A) (hB : Continuous B) (k : ℤ) :
    hermitianGradientColumns
      (∫ t in (0 : ℝ)..1, wave (-k) (2*t) • A t)
      (∫ t in (0 : ℝ)..1, wave (-k) (2*t) • B t) =
      ∫ t in (0 : ℝ)..1, wave (-k) (2*t) • hermitianGradientColumns (A t) (B t) := by
  have hw : Continuous (fun t : ℝ => wave (-k) (2*t)) :=
    (continuous_wave (-k)).comp (continuous_const.mul continuous_id)
  have hAi : IntervalIntegrable (fun t => wave (-k) (2*t) • A t) volume 0 1 :=
    (hw.smul hA).intervalIntegrable 0 1
  have hBi : IntervalIntegrable (fun t => wave (-k) (2*t) • B t) volume 0 1 :=
    (hw.smul hB).intervalIntegrable 0 1
  have h0 : IntervalIntegrable (fun t => hermitianGradientLift 0 (wave (-k) (2*t) • A t)) volume 0 1 :=
    ((hermitianGradientLift 0).continuous.comp (hw.smul hA)).intervalIntegrable 0 1
  have h1 : IntervalIntegrable (fun t => hermitianGradientLift 1 (wave (-k) (2*t) • B t)) volume 0 1 :=
    ((hermitianGradientLift 1).continuous.comp (hw.smul hB)).intervalIntegrable 0 1
  unfold hermitianGradientColumns
  rw [← (hermitianGradientLift 0).intervalIntegral_comp_comm hAi,
    ← (hermitianGradientLift 1).intervalIntegral_comp_comm hBi,
    ← intervalIntegral.integral_add h0 h1]
  congr 1
  funext t
  simp only [map_smul,smul_add]

end NLS.ComplexAnalysis
