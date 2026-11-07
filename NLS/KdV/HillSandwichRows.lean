import NLS.KdV.HillWeightedReciprocal

/-! Weighted double-reciprocal rows for the actual periodic half-denominator
sandwich. The power remains sharp enough for every original -1<t<-1/2. -/
noncomputable section
open Set Metric
namespace NLS.KdV

/-- The squared source Sobolev weight of a difference is controlled by
the sum of the two squared weights, throughout 0<=r<=1. -/
theorem sobolev_sub_sq_le_sum (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) (l m : ℤ) :
    (Weight.sobolev r (l-m))^2 ≤ 4*((Weight.sobolev r l)^2+(Weight.sobolev r m)^2) := by
  have hw (k : ℤ) : (Weight.sobolev r k)^2 = (1+|(k:ℝ)|)^(2*r) := by
    rw [Weight.sobolev_apply,← Real.rpow_mul_natCast (by positivity)]
    congr 1
    ring
  rw [hw,hw,hw]
  have htri : 1+|((l-m:ℤ):ℝ)| ≤ (1+|(l:ℝ)|)+(1+|(m:ℝ)|) := by
    simp only [Int.cast_sub]
    have ht := norm_sub_le (l:ℝ) (m:ℝ)
    simp only [Real.norm_eq_abs] at ht
    linarith
  have haux (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hab : A ≤ 2*B) :
      A^(2*r) ≤ 4*B^(2*r) := by
    calc
      _ ≤ (2*B)^(2*r) := Real.rpow_le_rpow hA hab (by positivity)
      _ = 2^(2*r)*B^(2*r) := Real.mul_rpow (by norm_num) hB
      _ ≤ _ := mul_le_mul_of_nonneg_right
        ((Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
          (show 2*r ≤ 2 by linarith)).trans_eq (by norm_num)) (by positivity)
  rcases le_total (1+|(l:ℝ)|) (1+|(m:ℝ)|) with h | h
  · have hb := haux (1+|((l-m:ℤ):ℝ)|) (1+|(m:ℝ)|) (by positivity) (by positivity) (by linarith)
    have hp : 0 ≤ (1+|(l:ℝ)|)^(2*r) := by positivity
    linarith
  · have hb := haux (1+|((l-m:ℤ):ℝ)|) (1+|(l:ℝ)|) (by positivity) (by positivity) (by linarith)
    have hp : 0 ≤ (1+|(m:ℝ)|)^(2*r) := by positivity
    linarith

/-- A weighted full double-reciprocal row is dominated by TWO translated
full reciprocal lattices, with no removed resonances or potential assumptions. -/
theorem hillSandwich_row_majorant (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ∈ sphere (freeHillValue n:ℂ) (n:ℝ)) (k m : ℤ) :
    (Weight.sobolev r k)^2 * ‖z-(freeHillValue (m+k):ℂ)‖⁻¹ * ‖z-(freeHillValue m:ℂ)‖⁻¹ ≤
      64*(n:ℝ)^(2*r-1)*(‖z-(freeHillValue m:ℂ)‖⁻¹+‖z-(freeHillValue (m+k):ℂ)‖⁻¹) := by
  have hw := sobolev_sub_sq_le_sum r hr hr1 (m+k) m
  simp only [add_sub_cancel_left] at hw
  have hL := freeHillSourceCircle_weighted_reciprocal_le r hr hr1 n hn z hz (m+k)
  have hM := freeHillSourceCircle_weighted_reciprocal_le r hr hr1 n hn z hz m
  have h := add_le_add
    (mul_le_mul_of_nonneg_right hL (by positivity : 0 ≤ ‖z-(freeHillValue m:ℂ)‖⁻¹))
    (mul_le_mul_of_nonneg_right hM (by positivity : 0 ≤ ‖z-(freeHillValue (m+k):ℂ)‖⁻¹))
  calc
    _ ≤ 4*((Weight.sobolev r (m+k))^2+(Weight.sobolev r m)^2)*
        ‖z-(freeHillValue (m+k):ℂ)‖⁻¹*‖z-(freeHillValue m:ℂ)‖⁻¹ := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hw (by positivity)) (by positivity)
    _ = 4*(((Weight.sobolev r (m+k))^2*‖z-(freeHillValue (m+k):ℂ)‖⁻¹)*‖z-(freeHillValue m:ℂ)‖⁻¹+
        ((Weight.sobolev r m)^2*‖z-(freeHillValue m:ℂ)‖⁻¹)*‖z-(freeHillValue (m+k):ℂ)‖⁻¹) := by ring
    _ ≤ 4*((16*(n:ℝ)^(2*r-1))*‖z-(freeHillValue m:ℂ)‖⁻¹+
        (16*(n:ℝ)^(2*r-1))*‖z-(freeHillValue (m+k):ℂ)‖⁻¹) :=
      mul_le_mul_of_nonneg_left h (by norm_num : (0:ℝ) ≤ 4)
    _ = _ := by ring

/-- Each weighted row is genuinely summable over all original signed modes. -/
theorem summable_hillSandwich_row (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ∈ sphere (freeHillValue n:ℂ) (n:ℝ)) (k : ℤ) :
    Summable (fun m : ℤ => (Weight.sobolev r k)^2 *
      ‖z-(freeHillValue (m+k):ℂ)‖⁻¹*‖z-(freeHillValue m:ℂ)‖⁻¹) := by
  have hs := summable_freeHillSourceCircle_reciprocal n hn z hz
  have ht : Summable (fun m : ℤ => ‖z-(freeHillValue (m+k):ℂ)‖⁻¹) :=
    hs.comp_injective (Equiv.addRight k).injective
  exact ((hs.add ht).mul_left (64*(n:ℝ)^(2*r-1))).of_nonneg_of_le
    (fun _ => by positivity) (hillSandwich_row_majorant r hr hr1 n hn z hz k)

/-- The weighted full row sum has the decay required by the rough-potential
Hilbert-Schmidt bound, uniformly over EVERY potential-frequency difference. -/
theorem tsum_hillSandwich_row_le_log (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (n : ℕ) (hn : 1 ≤ n) (hlog : 1 < Real.log (n:ℝ)) (z : ℂ)
    (hz : z ∈ sphere (freeHillValue n:ℂ) (n:ℝ)) (k : ℤ) :
    (∑' m : ℤ, (Weight.sobolev r k)^2 *
      ‖z-(freeHillValue (m+k):ℂ)‖⁻¹*‖z-(freeHillValue m:ℂ)‖⁻¹) ≤
      128*(8*Real.exp 1+2)*Real.log (n:ℝ)*(n:ℝ)^(2*r-2) := by
  have hs := summable_freeHillSourceCircle_reciprocal n hn z hz
  have ht : Summable (fun m : ℤ => ‖z-(freeHillValue (m+k):ℂ)‖⁻¹) :=
    hs.comp_injective (Equiv.addRight k).injective
  have he : (∑' m : ℤ, ‖z-(freeHillValue (m+k):ℂ)‖⁻¹) =
      ∑' m : ℤ, ‖z-(freeHillValue m:ℂ)‖⁻¹ :=
    (Equiv.addRight k).tsum_eq (fun m => ‖z-(freeHillValue m:ℂ)‖⁻¹)
  have hb := (summable_hillSandwich_row r hr hr1 n hn z hz k).tsum_le_tsum
    (hillSandwich_row_majorant r hr hr1 n hn z hz k) ((hs.add ht).mul_left _)
  rw [tsum_mul_left,hs.tsum_add ht,he] at hb
  have hfull := tsum_freeHillSourceCircle_reciprocal_le_log n hn hlog z hz
  have h := mul_le_mul_of_nonneg_left (add_le_add hfull hfull)
    (show 0 ≤ 64*(n:ℝ)^(2*r-1) by positivity)
  have hp : (n:ℝ)^(2*r-1)*(n:ℝ)⁻¹ = (n:ℝ)^(2*r-2) := by
    rw [← Real.rpow_neg_one,← Real.rpow_add (by exact_mod_cast hn : (0:ℝ) < n)]
    congr 1
    ring
  apply hb.trans
  apply h.trans_eq
  calc
    _ = (128*(8*Real.exp 1+2)*Real.log (n:ℝ))*((n:ℝ)^(2*r-1)*(n:ℝ)⁻¹) := by ring
    _ = _ := by rw [hp]

end NLS.KdV
