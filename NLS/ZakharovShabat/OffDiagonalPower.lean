import NLS.ZakharovShabat.OffDiagonalTailBound
import NLS.ZakharovShabat.DoubleReciprocalSummability
import Mathlib.Analysis.MeanInequalitiesPow

/-!
# Summation of the refined off-diagonal majorant

The two reciprocal-region sums combine with the two potential factors. The
near contribution retains the product of the actual potential tails.
-/

noncomputable section
open scoped ENNReal NNReal
namespace NLS.ZakharovShabat

/-- The scalar two-region estimate preserves both potential factors in the power sum. -/
theorem summable_two_region_power {P D T : ℝ} (hP : 1 ≤ P) (hD : 0 ≤ D) (hT : 0 ≤ T)
    (F G : ℤ → ℝ) (hF : ∀ n, 0 ≤ F n) (hG : ∀ n, 0 ≤ G n)
    (hsF : Summable (fun n => (F n)^P)) (hsG : Summable (fun n => (G n)^P)) :
    Summable (fun n => (2*D*(2*D*F n+T*G n))^P) ∧
      (∑' n, (2*D*(2*D*F n+T*G n))^P) ≤
        (4 : ℝ)^P * 2^(P-1) * D^P * (D^P * ∑' n, (F n)^P + T^P * ∑' n, (G n)^P) := by
  have hpoint (n : ℤ) : (2*D*(2*D*F n+T*G n))^P ≤
      (4 : ℝ)^P * 2^(P-1) * D^P * (D^P*(F n)^P+T^P*(G n)^P) := by
    have hFn := hF n
    have hGn := hG n
    have hmean : (D*F n+T*G n)^P ≤ (2 : ℝ)^(P-1)*((D*F n)^P+(T*G n)^P) := by
      exact_mod_cast NNReal.rpow_add_le_mul_rpow_add_rpow
        (⟨D*F n, mul_nonneg hD (hF n)⟩ : ℝ≥0) (⟨T*G n, mul_nonneg hT (hG n)⟩ : ℝ≥0) hP
    calc
      _ ≤ (4*D*(D*F n+T*G n))^P := by
        apply Real.rpow_le_rpow (by positivity) _ (zero_le_one.trans hP)
        nlinarith [mul_nonneg hD (mul_nonneg hT (hG n))]
      _ = (4 : ℝ)^P * D^P * (D*F n+T*G n)^P := by
        rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by norm_num) hD]
      _ ≤ (4 : ℝ)^P * D^P * ((2 : ℝ)^(P-1)*((D*F n)^P+(T*G n)^P)) :=
        mul_le_mul_of_nonneg_left hmean (by positivity)
      _ = _ := by rw [Real.mul_rpow hD (hF n), Real.mul_rpow hT (hG n)]; ring
  have hs := ((hsF.mul_left (D^P)).add (hsG.mul_left (T^P))).mul_left ((4 : ℝ)^P * 2^(P-1) * D^P)
  have hactual := hs.of_nonneg_of_le (fun n => by
    have hFn := hF n
    have hGn := hG n
    positivity) hpoint
  refine ⟨hactual, (hactual.tsum_le_tsum hpoint hs).trans_eq ?_⟩
  rw [tsum_mul_left, (hsF.mul_left (D^P)).tsum_add (hsG.mul_left (T^P)), tsum_mul_left, tsum_mul_left]

/-- A constant depending only on the exponent for the refined regional sum. -/
def offDiagonalRegionConstant (p : ℝ≥0∞) : ℝ :=
  (4 : ℝ)^p.toReal * 2^(p.toReal-1) * doubleReciprocalSummationConstant p

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
local instance : Fact (1 ≤ p.conjExponent) := ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩

/-- The complete majorant power series converges, with separate products of potential norms and tails. -/
theorem offDiagonalTailBound_summable_and_le (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (d a : WeightedCoeff w.toWeight p) (N : ℕ) (hN : 2 ≤ N) :
    Summable (fun n : ℤ => (offDiagonalTailBound hp w d a N n)^p.toReal) ∧
      (∑' n : ℤ, (offDiagonalTailBound hp w d a N n)^p.toReal) ≤
        offDiagonalRegionConstant p * ‖d‖^p.toReal *
          (‖d‖^p.toReal * ‖a‖^p.toReal / ((N/2 : ℕ) : ℝ)^(min 1 (p.toReal-1)) +
            ‖WeightedCoeff.fourierTail w.toWeight N d‖^p.toReal *
              ‖WeightedCoeff.fourierTail w.toWeight N a‖^p.toReal) := by
  let A := WeightedCoeff.weightEquiv w.toWeight p a
  have hq := (ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top
  let F := fun n : ℤ => ‖doubleReciprocalFarRow hq A (N/2) n‖
  let G := fun n : ℤ => ‖doubleReciprocalNearRow hq A N n‖
  obtain ⟨hsF,hF⟩ := doubleReciprocalFarRow_summable_and_le hp hp1 A (N/2) (by omega)
  obtain ⟨hsG,hG⟩ := doubleReciprocalNearRow_summable_and_le hp hp1 A N
  have hP : 1 ≤ p.toReal := (ENNReal.toReal_le_toReal (by simp) hp).mpr hp1.le
  obtain ⟨hc, hb⟩ := summable_two_region_power hP (norm_nonneg d)
    (norm_nonneg (WeightedCoeff.fourierTail w.toWeight N d)) F G
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) hsF hsG
  refine ⟨hc, hb.trans ?_⟩
  calc
    _ ≤ (4 : ℝ)^p.toReal * 2^(p.toReal-1) * ‖d‖^p.toReal *
        (‖d‖^p.toReal * (doubleReciprocalSummationConstant p * ‖A‖^p.toReal /
          ((N/2 : ℕ) : ℝ)^(min 1 (p.toReal-1))) +
        ‖WeightedCoeff.fourierTail w.toWeight N d‖^p.toReal *
          (doubleReciprocalSummationConstant p * ‖Coeff.fourierTail N A‖^p.toReal)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add (mul_le_mul_of_nonneg_left hF (by positivity)) (mul_le_mul_of_nonneg_left hG (by positivity))
    _ = _ := by
      have ha : ‖A‖ = ‖a‖ := (WeightedCoeff.norm_eq w.toWeight p a).symm
      have ht : ‖Coeff.fourierTail N A‖ = ‖WeightedCoeff.fourierTail w.toWeight N a‖ := by
        rw [← WeightedCoeff.weightEquiv_fourierTail]
        exact (WeightedCoeff.norm_eq w.toWeight p _).symm
      rw [ha, ht]
      unfold offDiagonalRegionConstant
      ring

end NLS.ZakharovShabat
