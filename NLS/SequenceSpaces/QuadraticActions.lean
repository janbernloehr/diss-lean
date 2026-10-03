import NLS.SequenceSpaces.DoublingProduct
import NLS.SequenceSpaces.RealCoeff
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! # Quadratic action sequences on Hilbert outputs

The coordinate formula `(xₙ² + yₙ²)/2` defines an entire map from two
complex ℓ² spaces to ℓ¹. Its real restriction is nonnegative and its
sum is exactly half the sum of the two squared Hilbert norms.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS

/-- The complex quadratic action map, with values in the actual ℓ¹ space. -/
def quadraticActions (z : Coeff 2 × Coeff 2) : Coeff 1 :=
  (1/2 : ℂ) • (Coeff.doublingProduct z.1 z.1 + Coeff.doublingProduct z.2 z.2)

@[simp] theorem quadraticActions_apply (z : Coeff 2 × Coeff 2) (n : ℤ) :
    quadraticActions z n = (z.1 n ^ 2 + z.2 n ^ 2)/2 := by
  change (1/2 : ℂ) * (z.1 n * z.1 n + z.2 n * z.2 n) = _
  ring

/-- Quadratic actions depend holomorphically in ℓ¹ norm on both ℓ² inputs. -/
theorem analyticOnNhd_quadraticActions : AnalyticOnNhd ℂ quadraticActions univ := by
  intro z _
  have hx := (ContinuousLinearMap.fst ℂ (Coeff 2) (Coeff 2)).analyticAt z
  have hy := (ContinuousLinearMap.snd ℂ (Coeff 2) (Coeff 2)).analyticAt z
  exact (((Coeff.doublingProduct (p := 1) (q := 2)).analyticAt_bilinear _).comp₂ hx hx).add
    (((Coeff.doublingProduct (p := 1) (q := 2)).analyticAt_bilinear _).comp₂ hy hy) |>.const_smul (c := (1/2 : ℂ))

/-- The real quadratic action sequence. -/
def realQuadraticActions (z : RealCoeff 2 × RealCoeff 2) : RealCoeff 1 :=
  Coeff.reCLM 1 (quadraticActions (((RealCoeff.complexCLM 2).prodMap (RealCoeff.complexCLM 2)) z))

@[simp] theorem realQuadraticActions_apply (z : RealCoeff 2 × RealCoeff 2) (n : ℤ) :
    realQuadraticActions z n = (z.1 n ^ 2 + z.2 n ^ 2)/2 := by
  simp [realQuadraticActions, ← Complex.ofReal_pow]

theorem realQuadraticActions_nonneg (z : RealCoeff 2 × RealCoeff 2) (n : ℤ) :
    0 ≤ realQuadraticActions z n := by rw [realQuadraticActions_apply]; positivity

/-- Real quadratic actions are real analytic in ℓ¹ norm. -/
theorem analyticOnNhd_realQuadraticActions : AnalyticOnNhd ℝ realQuadraticActions univ := by
  intro z _
  exact ((Coeff.reCLM 1).analyticAt _).comp
    (((analyticOnNhd_quadraticActions _ (mem_univ _)).restrictScalars (𝕜 := ℝ)).comp
      (((RealCoeff.complexCLM 2).prodMap (RealCoeff.complexCLM 2)).analyticAt z))

/-- The sum of the real actions, as a continuous-linear sum after the quadratic map. -/
def realQuadraticActionTotal (z : RealCoeff 2 × RealCoeff 2) : ℝ :=
  lp.tsumCLM ℝ ℤ ℝ (realQuadraticActions z)

/-- Absolute convergence of the literal action series. -/
theorem summable_realQuadraticActions (z : RealCoeff 2 × RealCoeff 2) :
    Summable (fun n : ℤ => realQuadraticActions z n) :=
  (realQuadraticActions z).property.summable_of_one

/-- The exact total uses the sum of component norm squares, not the
square of the maximum norm on the ordinary product. -/
theorem realQuadraticActionTotal_eq (z : RealCoeff 2 × RealCoeff 2) :
    realQuadraticActionTotal z = (‖z.1‖^2 + ‖z.2‖^2)/2 := by
  have hsq (a : RealCoeff 2) : Summable (fun n : ℤ => (a n)^2) := by
    have h := (lp.memℓp a).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    simpa [Real.rpow_two] using h
  have hnorm (a : RealCoeff 2) : (∑' n : ℤ, (a n)^2) = ‖a‖^2 := by
    have h := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) a
    simpa [Real.rpow_two] using h.symm
  change (∑' n : ℤ, realQuadraticActions z n) = _
  simp only [realQuadraticActions_apply, tsum_div_const]
  rw [(hsq z.1).tsum_add (hsq z.2), hnorm, hnorm]

/-- Since each action is nonnegative, its ℓ¹ norm is its total. -/
theorem norm_realQuadraticActions (z : RealCoeff 2 × RealCoeff 2) :
    ‖realQuadraticActions z‖ = realQuadraticActionTotal z := by
  rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (1 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_one, Real.rpow_one, one_div_one]
  change (∑' n : ℤ, ‖realQuadraticActions z n‖) = ∑' n : ℤ, realQuadraticActions z n
  apply tsum_congr
  intro n
  exact Real.norm_of_nonneg (realQuadraticActions_nonneg z n)

end NLS
