import NLS.KdV.HminusOneCanonicalHillPsiPeriods
import NLS.KdV.HminusOneHillPsiRealZeros

/-! Intrinsic numerators retain arbitrary-reference-shift sub-sine
growth at EVERY complex source in the common domain and actual retained
zeros in EVERY original real gap. Growth cutoffs are pointwise in the
source, numerator index and reference shift. No unique-zero, product or
locally uniform all-index estimate is inferred here. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.KdV

theorem hillHminusCanonicalPsi_arbitrary_shift_sub_sine (n : ℕ+) (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusCanonicalPsiDomain) (c : ℂ) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∀ z ∈ sphere (0:ℂ) (centralCircleRadius k),
      ‖(2*z*hillHminusCanonicalPsi n (z^2-c,q))/(-2*sin z)‖ ≤ ε := by
  obtain ⟨B,hB⟩ := mem_iUnion.mp hq
  simp_rw [B.canonical_numerator_eq n _ q hB]
  exact B.parent.psiNumerator_arbitrary_shift_pullback_sub_sine B.family q n c ε hε

theorem exists_hillHminusCanonicalPsi_zero_in_original_gap
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (n m : ℕ+) (hmn : m ≠ n) :
    ∃ E : ℝ, E ∈ Icc (hillHminusLabels q hr (2*(m:ℕ)-1)) (hillHminusLabels q hr (2*(m:ℕ))) ∧
      hillHminusCanonicalPsi n ((E:ℂ),q) = 0 := by
  obtain ⟨B,hB⟩ := mem_iUnion.mp (real_mem_hillHminusCanonicalPsiDomain q hr)
  obtain ⟨E,hE,hzero⟩ := B.parent.exists_psiNumerator_zero_in_original_gap B.family q (B.subset hB) hr n m hmn
  refine ⟨E,hE,?_⟩
  rw [B.canonical_numerator_eq n (E:ℂ) q hB]
  exact hzero

theorem hillHminusCanonicalPsi_zero_at_real_collapsed_gap
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (n m : ℕ+) (hmn : m ≠ n)
    (hc : hillHminusLabels q hr (2*(m:ℕ)-1) = hillHminusLabels q hr (2*(m:ℕ))) :
    hillHminusCanonicalPsi n ((hillHminusLabels q hr (2*(m:ℕ)):ℂ),q) = 0 := by
  obtain ⟨E,hE,hzero⟩ := exists_hillHminusCanonicalPsi_zero_in_original_gap q hr n m hmn
  have he : E = hillHminusLabels q hr (2*(m:ℕ)) := by rw [hc] at hE; exact le_antisymm hE.2 hE.1
  simpa only [he] using hzero

end NLS.KdV
