import NLS.KdV.HillMiuraNormalizedRatioLocalData
import NLS.KdV.HillHminusOneCanonicalQuotients

/-! The intrinsic canonical action ratio is REAL POSITIVE on the
ENTIRE native real form, including REAL closed gaps. The identically
collapsed-gap convention is handled explicitly, not excluded by density. -/
noncomputable section
open Set Metric Complex
open scoped Classical
namespace NLS.KdV

theorem hillHminusCanonicalActionRatio_real_positive (n : ℕ+) (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) :
    (hillHminusCanonicalActionRatio n q).im = 0 ∧ 0 < (hillHminusCanonicalActionRatio n q).re := by
  by_cases hz : ∀ a ∈ hillHminusCanonicalRatioDomain, hillHminusCanonicalGapSquare n a = 0
  · rw [hillHminusCanonicalActionRatio,if_pos hz]
    norm_num
  · have hne : ∃ a ∈ hillHminusCanonicalRatioDomain, hillHminusCanonicalGapSquare n a ≠ 0 := by simpa using hz
    obtain ⟨B,hB⟩ := exists_hillHminusMiuraGapBall q hr
    obtain ⟨U,hU,hqU,_,hR,hfactor⟩ := B.exists_local_normalizedRatio_data n q hB hr
    let V := U ∩ hillHminusCanonicalRatioDomain
    have hV : IsOpen V := hU.inter isOpen_hillHminusCanonicalRatioDomain
    have hqV : q ∈ V := ⟨hqU,real_mem_hillHminusCanonicalRatioDomain q hr⟩
    have he := hillHminusCanonicalActionRatio_unique_on_open n V hV inter_subset_right
      (B.normalizedRatio n) (hR.mono inter_subset_left) hne (fun a ha => (hfactor a ha.1).2.1)
    rw [he hqV]
    exact B.normalizedRatio_real_positive n q hB hr

end NLS.KdV
