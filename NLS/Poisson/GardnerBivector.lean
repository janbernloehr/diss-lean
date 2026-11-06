import NLS.SequenceSpaces.SobolevBilinearPairing
import NLS.SequenceSpaces.WeightedMultiplier
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! The scalar unit-period Gardner pairing on actual H1 cotangents.
The frequency is 2*pi*k, the Fourier pairing reverses indices, and all
series converge absolutely. This is distinct from the two-field NLS bracket. -/
noncomputable section
open Complex
open scoped ENNReal
namespace NLS.Poisson

theorem gardnerDerivative_weight_bound (k : ℤ) :
    Weight.sobolev (-1) k*‖(2*Real.pi:ℂ)*I*k‖ ≤ (2*Real.pi)*Weight.sobolev 1 k := by
  simp only [Weight.sobolev_apply,Real.rpow_neg_one,Real.rpow_one,norm_mul,norm_I,
    mul_one,Complex.norm_intCast,Complex.norm_real,Real.norm_eq_abs]
  norm_num [abs_of_pos Real.pi_pos]
  have h : |(k:ℝ)|/(1+|(k:ℝ)|) ≤ 1+|(k:ℝ)| :=
    (div_le_iff₀ (by positivity)).mpr (by nlinarith [abs_nonneg (k:ℝ)])
  calc
    _ = (2*Real.pi)*(|(k:ℝ)|/(1+|(k:ℝ)|)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h (by positivity)

def gardnerDerivative :
    WeightedCoeff (Weight.sobolev 1) 2 →L[ℂ] WeightedCoeff (Weight.sobolev (-1)) 2 :=
  WeightedCoeff.weightedMultiplierCLM _ _ (fun k => (2*Real.pi:ℂ)*I*k)
    (2*Real.pi) (by positivity) gardnerDerivative_weight_bound

theorem gardnerDerivative_apply (a : WeightedCoeff (Weight.sobolev 1) 2) (k : ℤ) :
    (gardnerDerivative a).val k=(2*Real.pi:ℂ)*I*k*a.val k := rfl

theorem norm_gardnerDerivative_le (a : WeightedCoeff (Weight.sobolev 1) 2) :
    ‖gardnerDerivative a‖ ≤ (2*Real.pi)*‖a‖ :=
  WeightedCoeff.norm_weightedMultiplier_le _ _ _ _ (by positivity) gardnerDerivative_weight_bound a

def gardnerBivector : WeightedCoeff (Weight.sobolev 1) 2 →L[ℂ]
    WeightedCoeff (Weight.sobolev 1) 2 →L[ℂ] ℂ :=
  (WeightedCoeff.sobolevBilinearPairing (p := 2) (q := 2) 1).bilinearComp
    (ContinuousLinearMap.id ℂ _) gardnerDerivative

theorem gardnerBivector_eq_tsum (a b : WeightedCoeff (Weight.sobolev 1) 2) :
    gardnerBivector a b=∑' k : ℤ, a.val k*((2*Real.pi:ℂ)*I*(-k)*b.val (-k)) := by
  change WeightedCoeff.sobolevBilinearPairing 1 a (gardnerDerivative b)=_
  rw [WeightedCoeff.sobolevBilinearPairing_apply]
  exact tsum_congr (fun k => by rw [gardnerDerivative_apply,Int.cast_neg])

theorem summable_norm_gardnerBivector (a b : WeightedCoeff (Weight.sobolev 1) 2) :
    Summable (fun k : ℤ => ‖a.val k*((2*Real.pi:ℂ)*I*(-k)*b.val (-k))‖) := by
  simpa only [gardnerDerivative_apply,Int.cast_neg] using
    WeightedCoeff.summable_norm_sobolevBilinearPairing 1 a (gardnerDerivative b)

theorem norm_gardnerBivector_le (a b : WeightedCoeff (Weight.sobolev 1) 2) :
    ‖gardnerBivector a b‖ ≤ (2*Real.pi)*‖a‖*‖b‖ := by
  apply (WeightedCoeff.norm_sobolevBilinearPairing_le 1 a (gardnerDerivative b)).trans
  have h := mul_le_mul_of_nonneg_left (norm_gardnerDerivative_le b) (norm_nonneg a)
  simpa only [mul_left_comm,mul_assoc] using h

theorem gardnerBivector_antisymm (a b : WeightedCoeff (Weight.sobolev 1) 2) :
    gardnerBivector a b= -gardnerBivector b a := by
  rw [gardnerBivector_eq_tsum,gardnerBivector_eq_tsum,← tsum_neg]
  rw [← (Equiv.neg ℤ).tsum_eq (fun k : ℤ => -(b.val k*((2*Real.pi:ℂ)*I*(-k)*a.val (-k))))]
  apply tsum_congr
  intro k
  simp only [Equiv.neg_apply,neg_neg,Int.cast_neg]
  ring

theorem gardnerBivector_self (a : WeightedCoeff (Weight.sobolev 1) 2) : gardnerBivector a a=0 := by
  have h := gardnerBivector_antisymm a a
  linear_combination (1/2:ℂ)*h

theorem analyticOnNhd_gardnerBivector {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (a b : E → WeightedCoeff (Weight.sobolev 1) 2) {U : Set E}
    (ha : AnalyticOnNhd ℂ a U) (hb : AnalyticOnNhd ℂ b U) :
    AnalyticOnNhd ℂ (fun q => gardnerBivector (a q) (b q)) U := by
  intro q hq
  exact (gardnerBivector.analyticAt_bilinear _).comp₂ (ha q hq) (hb q hq)

end NLS.Poisson
