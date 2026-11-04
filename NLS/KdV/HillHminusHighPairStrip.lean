import NLS.KdV.HillHminusOneHighGapPairs
import NLS.KdV.HillReduction

/-! Actual H-minus-one high energy discs lie in the same original
Fourier reduction strip, retaining their literal positive index. -/
noncomputable section
open Set Metric Complex
namespace NLS.KdV

theorem hillHminusGapSquareDisc_subset_reducedHillStrip (n : ℕ+) (r : ℝ)
    (hr : r ≤ Real.pi/4) : hillHminusGapSquareDisc n r ⊆ reducedHillStrip (n:ℕ) := by
  intro z hz
  have he : ‖z-(((Real.pi:ℂ)*(n:ℕ))^2)‖ ≤ Real.pi*(n:ℕ)*r := by
    simpa only [hillHminusGapSquareDisc,classicalHillGapSquareDisc,mem_closedBall,dist_eq_norm] using hz
  have hre := (Complex.abs_re_le_norm (z-(((Real.pi:ℂ)*(n:ℕ))^2))).trans he
  have hcenter : ((((Real.pi:ℂ)*(n:ℕ))^2)).re=freeHillValue (n:ℕ) := by
    have hc : ((Real.pi:ℂ)*(n:ℕ))^2=(freeHillValue (n:ℕ):ℂ) := by
      unfold freeHillValue
      push_cast
      ring
    rw [hc,Complex.ofReal_re]
  rw [Complex.sub_re,hcenter] at hre
  change |z.re-freeHillValue (n:ℕ)| ≤ 6*(n:ℕ)
  apply hre.trans
  have hπ : Real.pi^2/4 < 6 := by nlinarith [Real.pi_lt_four,Real.pi_pos]
  have hn : (0:ℝ) ≤ (n:ℕ) := Nat.cast_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hr (mul_nonneg Real.pi_pos.le hn)
  nlinarith

end NLS.KdV
