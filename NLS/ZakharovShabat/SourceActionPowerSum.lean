import NLS.ZakharovShabat.SourceActionPowerConstant
import NLS.SequenceSpaces.RealActionReduction

set_option autoImplicit false
noncomputable section
open Set
open scoped ENNReal
namespace NLS.RealCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

omit [Fact (1 ≤ p)] in
/-- The quadratic action power is bounded by the full coordinate power sum below two. -/
theorem pairAction_rpow_le_coordinate_powers (r : ℝ) (hr : 0 < r) (hr2 : r ≤ 2)
    (z : RealCoeff p × RealCoeff p) (n : ℤ) :
    (pairAction z n)^(r/2) ≤ |z.1 n|^r+|z.2 n|^r := by
  have he (x : ℝ) : (x^2)^(r/2) = |x|^r := by
    rw [← sq_abs,← Real.rpow_two,← Real.rpow_mul (abs_nonneg x)]
    congr 1
    ring
  have ha : 0 ≤ pairAction z n := by dsimp only [pairAction]; positivity
  have hb : pairAction z n ≤ (z.1 n)^2+(z.2 n)^2 := by
    dsimp only [pairAction]
    nlinarith [sq_nonneg (z.1 n),sq_nonneg (z.2 n)]
  exact (Real.rpow_le_rpow ha hb (by linarith)).trans (by
    simpa only [he] using Real.rpow_add_le_add_rpow (sq_nonneg (z.1 n))
      (sq_nonneg (z.2 n)) (by linarith : 0 ≤ r/2) (by linarith : r/2 ≤ 1))

/-- Actual lp coordinates give a summable action-power sequence; no formal tsum is assumed finite. -/
theorem summable_pairAction_rpow (hp : p ≠ ⊤) (hp2 : p ≤ 2)
    (z : RealCoeff p × RealCoeff p) :
    Summable (fun n => (pairAction z n)^(p.toReal/2)) := by
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hp
  have hr2 : p.toReal ≤ 2 := by
    simpa using (ENNReal.toReal_le_toReal hp (by norm_num : (2:ℝ≥0∞)≠⊤)).mpr hp2
  have hs := ((lp.memℓp z.1).summable hp0).add ((lp.memℓp z.2).summable hp0)
  apply Summable.of_nonneg_of_le (fun n => Real.rpow_nonneg (by dsimp only [pairAction]; positivity) _)
    (fun n => pairAction_rpow_le_coordinate_powers p.toReal hp0 hr2 z n)
  simpa only [Real.norm_eq_abs] using hs

/-- Corrected literal summed norm-to-action bound, retaining both coordinates. -/
theorem coordinate_power_tsum_le_two_actions (hp : p ≠ ⊤) (hp2 : p ≤ 2)
    (z : RealCoeff p × RealCoeff p) :
    (∑' n : ℤ, (|z.1 n|^p.toReal+|z.2 n|^p.toReal)) ≤
      2*(∑' n : ℤ, (pairAction z n)^(p.toReal/2)) := by
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hp
  have hr2 : p.toReal ≤ 2 := by
    simpa using (ENNReal.toReal_le_toReal hp (by norm_num : (2:ℝ≥0∞)≠⊤)).mpr hp2
  have hs : Summable (fun n : ℤ => |z.1 n|^p.toReal+|z.2 n|^p.toReal) := by
    simpa only [Real.norm_eq_abs] using
      ((lp.memℓp z.1).summable hp0).add ((lp.memℓp z.2).summable hp0)
  have ha := summable_pairAction_rpow hp hp2 z
  calc
    _ ≤ ∑' n : ℤ, 2*(pairAction z n)^(p.toReal/2) :=
      hs.tsum_le_tsum (fun n => ZakharovShabat.real_pair_power_le_two_action
        p.toReal hp0 hr2 (z.1 n) (z.2 n)) (ha.mul_left 2)
    _ = _ := tsum_mul_left

end NLS.RealCoeff

namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
  {W₀ B W : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The corrected summed bound uses the original spectral actions and actual map at every source. -/
theorem corrected_action_power_sum (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (hp2 : p ≤ 2) (φ : realTypeSourceSubmodule p) :
    Summable (fun n : ℤ => |(sourceRealAction hp hp1 φ.val φ.property n).re|^(p.toReal/2)) ∧
      (∑' n : ℤ, (|(sourceRealBirkhoffMap hp hp1 s φ).1 n|^p.toReal+
        |(sourceRealBirkhoffMap hp hp1 s φ).2 n|^p.toReal)) ≤
      2*(∑' n : ℤ, |(sourceRealAction hp hp1 φ.val φ.property n).re|^(p.toReal/2)) := by
  let z := sourceRealBirkhoffMap hp hp1 s φ
  have he (n : ℤ) : RealCoeff.pairAction z n = |(sourceRealAction hp hp1 φ.val φ.property n).re| := by
    have h := D.real_map_action_radius φ n
    have ha : 0 ≤ (sourceRealAction hp hp1 φ.val φ.property n).re := by
      nlinarith [sq_nonneg (z.1 n),sq_nonneg (z.2 n)]
    rw [abs_of_nonneg ha]
    dsimp only [RealCoeff.pairAction,z]
    linarith
  have hs := RealCoeff.summable_pairAction_rpow hp hp2 z
  have hb := RealCoeff.coordinate_power_tsum_le_two_actions hp hp2 z
  simp_rw [he] at hs hb
  exact ⟨hs,hb⟩

end NLS.ZakharovShabat.SourceBirkhoffMapComplexData
