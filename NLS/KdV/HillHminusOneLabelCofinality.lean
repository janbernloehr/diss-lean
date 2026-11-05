import NLS.KdV.HillHminusOneCanonicalRealLabels
import NLS.KdV.HillHminusOneLabelUniqueness

/-! # Cofinality of the actual canonical H^-1 gap endpoints -/
noncomputable section
set_option autoImplicit false
open Set Complex
namespace NLS.KdV

theorem nat_le_hillCentralSeparator (N : ℕ) (hN : 2 ≤ N) : (N : ℝ) ≤ hillCentralSeparator N := by
  have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hpi : (9 : ℝ) ≤ Real.pi^2 := by nlinarith [Real.pi_gt_three]
  have hp := mul_nonneg (sub_nonneg.mpr hpi) (sq_nonneg (N : ℝ))
  have hN₂ := mul_nonneg (show 0 ≤ (N : ℝ) by linarith) (show 0 ≤ (N : ℝ)-2 by linarith)
  unfold hillCentralSeparator freeHillValue
  push_cast
  nlinarith

theorem exists_hillHminusRealLabels_gap_upper_ge (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (x : ℝ) :
    ∃ m : ℕ, x ≤ hillHminusRealLabels q hr (2*(m+1)) := by
  obtain ⟨M,hM⟩ := exists_nat_gt x
  obtain ⟨N,r,V,hMN,hN,_,hqV,hspec⟩ := exists_hillHminusRealLabels_common_spec q (M+2)
  have h := (hspec q hqV hr).tail_above_separator (2*(N+1)) (by omega)
  have hMN' : (M : ℝ) ≤ N := by exact_mod_cast (show M ≤ N by omega)
  exact ⟨N,(hM.trans_le (hMN'.trans (nat_le_hillCentralSeparator N hN))).le.trans h.le⟩

end NLS.KdV
