import NLS.KdV.HillHalfPotentialBase
import NLS.KdV.PeriodOneHminusOneOriginal

/-! Exact period-one extraction in the entire fractional Sobolev scale.
The raw even coefficients are unchanged and the norm cost is at most two.
-/
noncomputable section
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

theorem fractional_periodOne_weight_bound (r : ℝ) (hr1 : r ≤ 1) (k : ℤ) :
    Weight.sobolev (-r) k ≤ 2*(Weight.sobolev (-r)).pullback (Coeff.parityEmbedding 0) k := by
  have hmono : Weight.sobolev (1-r) k ≤ Weight.sobolev (1-r) (2*k) := by
    simp only [Weight.sobolev_apply,Int.cast_mul,Int.cast_ofNat,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
    exact Real.rpow_le_rpow (by positivity) (by linarith [abs_nonneg (k:ℝ)]) (by linarith)
  have hb := (periodOneOriginalWeight_bounds k).2
  have he (j : ℤ) : Weight.sobolev (-r) j = Weight.sobolev (-1) j*Weight.sobolev (1-r) j := by
    simp only [Weight.sobolev_apply]
    rw [← Real.rpow_add (by positivity : (0:ℝ)<1+|(j:ℝ)|)]
    congr 1
    ring
  change Weight.sobolev (-r) k ≤ 2*Weight.sobolev (-r) (Coeff.parityEmbedding 0 k)
  simp only [Coeff.parityEmbedding_apply,add_zero]
  have hb' : Weight.sobolev (-1) k ≤ 2*Weight.sobolev (-1) (2*k) := by
    simpa only [periodOneOriginalWeight,Weight.pullback_apply,Coeff.parityEmbedding_apply,add_zero] using hb
  rw [he k,he (2*k)]
  exact (mul_le_mul hb' hmono (le_of_lt ((Weight.sobolev (1-r)).positive k))
    (mul_nonneg (by norm_num) (le_of_lt ((Weight.sobolev (-1)).positive (2*k))))).trans_eq (by ring)

def hillFractionalPeriodOneExtract (r : ℝ) (hr1 : r ≤ 1) :
    WeightedCoeff (Weight.sobolev (-r)) 2 →L[ℂ] WeightedCoeff (Weight.sobolev (-r)) 2 :=
  (WeightedCoeff.weightedMultiplierCLM
    ((Weight.sobolev (-r)).pullback (Coeff.parityEmbedding 0)) (Weight.sobolev (-r))
    (fun _ => (1:ℂ)) 2 (by norm_num)
    (fun k => by simpa only [norm_one,mul_one] using fractional_periodOne_weight_bound r hr1 k)).comp
      (WeightedCoeff.restrictTwoCLM (Weight.sobolev (-r)) (Coeff.parityEmbedding 0))

theorem hillFractionalPeriodOneExtract_apply (r : ℝ) (hr1 : r ≤ 1)
    (q : WeightedCoeff (Weight.sobolev (-r)) 2) (k : ℤ) :
    (hillFractionalPeriodOneExtract r hr1 q).val k = q.val (2*k) := by
  change (1:ℂ)*(WeightedCoeff.restrictTwoCLM _ _ q).val k = _
  rw [one_mul,WeightedCoeff.restrictTwoCLM_apply]
  simp only [Coeff.parityEmbedding_apply,add_zero]

theorem norm_hillFractionalPeriodOneExtract_le (r : ℝ) (hr1 : r ≤ 1)
    (q : WeightedCoeff (Weight.sobolev (-r)) 2) :
    ‖hillFractionalPeriodOneExtract r hr1 q‖ ≤ 2*‖q‖ := by
  have hm : ∀ k, Weight.sobolev (-r) k*‖(1:ℂ)‖ ≤
      2*(Weight.sobolev (-r)).pullback (Coeff.parityEmbedding 0) k := by
    intro k
    simpa only [norm_one,mul_one] using fractional_periodOne_weight_bound r hr1 k
  change ‖WeightedCoeff.weightedMultiplier _ _ _ 2 hm
    (WeightedCoeff.restrictTwoCLM _ _ q)‖ ≤ _
  apply (WeightedCoeff.norm_weightedMultiplier_le _ _ _ 2 (by norm_num) hm _).trans
  exact mul_le_mul_of_nonneg_left (WeightedCoeff.norm_restrictTwoCLM_le _ _ q) (by norm_num)

theorem hillFractionalPeriodOneExtract_native (r : ℝ) (hr1 : r ≤ 1)
    (q : WeightedCoeff (Weight.sobolev (-r)) 2) :
    WeightedCoeff.sobolevInclusion (show (-1:ℝ) ≤ -r by linarith)
        (hillFractionalPeriodOneExtract r hr1 q) =
      periodOneOriginalExtract (hillHalfPotentialBase r hr1 q) := by
  apply Subtype.ext
  funext k
  rw [WeightedCoeff.sobolevInclusion_apply,hillFractionalPeriodOneExtract_apply,
    periodOneOriginalExtract_apply,hillHalfPotentialBase_coefficient]

end NLS.KdV
