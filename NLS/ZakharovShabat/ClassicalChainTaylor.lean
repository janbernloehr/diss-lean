import NLS.ZakharovShabat.ClassicalChainPerturbation
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Spectral Taylor coefficients are the normalized classical chain curves

The exact fixed-parameter inverse factorization gives a convergent geometric
series in the Banach space of whole solution curves. Its coefficients are the
repeated zero-initial forced solutions with the alternating spectral sign.
Every spectral derivative is therefore identified, including at multiple roots.
-/

noncomputable section
open Set Complex NLS.LinearVolterra
open scoped ENNReal NNReal
namespace NLS.ZakharovShabat

/-- A positive guaranteed radius for the fixed-parameter spectral expansion. -/
def classicalChainRadius (Φ : Curve (ℂ × ℂ)) (z : ℂ) : ℝ≥0∞ :=
  (‖classicalChainOperator Φ z‖₊ : ℝ≥0∞)⁻¹

theorem classicalChainRadius_pos (Φ : Curve (ℂ × ℂ)) (z : ℂ) : 0 < classicalChainRadius Φ z := by
  simp [classicalChainRadius]

/-- The formal spectral series obtained by evaluating the geometric operator inverse. -/
def classicalChainSeries (Φ : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ) :
    FormalMultilinearSeries ℂ ℂ (Curve (ℂ × ℂ)) :=
  (ContinuousLinearMap.apply ℂ (Curve (ℂ × ℂ)) (classicalSolutionCurve Φ z v)).compFormalMultilinearSeries
    (fun n => ContinuousMultilinearMap.mkPiRing ℂ (Fin n) ((-classicalChainOperator Φ z)^n))

/-- Negating the chain operator gives precisely the alternating spectral sign at every power. -/
theorem neg_classicalChainOperator_pow_apply (Φ : Curve (ℂ × ℂ)) (z : ℂ) (n : ℕ) (v : ℂ × ℂ) :
    ((-classicalChainOperator Φ z)^n) (classicalSolutionCurve Φ z v) =
      (-1 : ℂ)^n • classicalChainCurve Φ z n v := by
  induction n with
  | zero => simp [classicalChainCurve]
  | succ n ih =>
    rw [pow_succ',mul_apply_eq_comp,neg_apply,ih,map_smul,classicalChainCurve_succ]
    simp only [pow_succ,mul_neg_one]
    module

/-- Every multilinear coefficient is the corresponding signed forced-chain curve. -/
theorem classicalChainSeries_apply (Φ : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ)
    (n : ℕ) (w : Fin n → ℂ) :
    classicalChainSeries Φ z v n w =
      (∏ i, w i) • ((-1 : ℂ)^n • classicalChainCurve Φ z n v) := by
  change (∏ i, w i) • (((-classicalChainOperator Φ z)^n) (classicalSolutionCurve Φ z v)) = _
  rw [neg_classicalChainOperator_pow_apply]

/-- The fixed-base spectral expansion converges in the supremum norm of entire physical solution curves. -/
theorem hasFPowerSeriesOnBall_classicalSolutionCurve (Φ : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ) :
    HasFPowerSeriesOnBall (fun w => classicalSolutionCurve Φ w v) (classicalChainSeries Φ z v)
      z (classicalChainRadius Φ z) := by
  have hgeom := spectrum.hasFPowerSeriesOnBall_inverse_one_sub_smul ℂ (-classicalChainOperator Φ z)
  have h := (ContinuousLinearMap.apply ℂ (Curve (ℂ × ℂ)) (classicalSolutionCurve Φ z v)).comp_hasFPowerSeriesOnBall hgeom
  have hh : HasFPowerSeriesOnBall (fun h => classicalSolutionCurve Φ (z+h) v)
      (classicalChainSeries Φ z v) 0 (classicalChainRadius Φ z) := by
    convert! h using 1
    · funext h
      exact classicalSolutionCurve_add_spectral Φ z h v
    · unfold classicalChainRadius
      congr 1
      convert! congrArg (fun r : ℝ≥0 => (r : ℝ≥0∞)) (nnnorm_neg (classicalChainOperator Φ z)).symm using 1
  convert! hh.comp_sub z using 1
  · funext w
    congr 1
    ring
  · simp

/-- The actual convergent Taylor sum uses the signed normalized chain curves. -/
theorem hasSum_classicalChainCurve (Φ : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ) (h : ℂ)
    (hh : ‖h‖ₑ < classicalChainRadius Φ z) :
    HasSum (fun n => (-h)^n • classicalChainCurve Φ z n v) (classicalSolutionCurve Φ (z+h) v) := by
  have hs := (hasFPowerSeriesOnBall_classicalSolutionCurve Φ z v).hasSum
    (show h ∈ Metric.eball 0 (classicalChainRadius Φ z) by simpa using hh)
  convert! hs using 1
  funext n
  rw [classicalChainSeries_apply]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,smul_smul,← mul_pow,mul_neg_one]

/-- All spectral derivatives of the whole solution curve are the factorial-scaled signed chain curves. -/
theorem iteratedDeriv_classicalSolutionCurve (Φ : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ) (n : ℕ) :
    iteratedDeriv n (fun w => classicalSolutionCurve Φ w v) z =
      n.factorial • ((-1 : ℂ)^n • classicalChainCurve Φ z n v) := by
  rw [iteratedDeriv_eq_iteratedFDeriv]
  have h := (hasFPowerSeriesOnBall_classicalSolutionCurve Φ z v).factorial_smul (1 : ℂ) n
  simpa only [classicalChainSeries_apply,Finset.prod_const_one,one_smul] using h.symm

end NLS.ZakharovShabat
