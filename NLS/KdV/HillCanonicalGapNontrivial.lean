import NLS.KdV.HillRealOpenGapDensity
import NLS.ComplexAnalysis.AnalyticFactorNontrivial

/-! EVERY actual positive Hill gap is nontrivial. Its analytic squared
gap cannot vanish identically on any nonempty open part of the common
complex domain. The original mean-zero real source already supplies witnesses. -/
noncomputable section
open Set Metric Complex
namespace NLS.KdV

theorem exists_real_mean_zero_native_gap_ne_zero (n : ℕ+) :
    ∃ q : PeriodOneHminusOne, IsRealPeriodOneHminusOne q ∧ q.val 0=0 ∧
      hillHminusCanonicalGapSquare n q ≠ 0 := by
  obtain ⟨a,_,ha⟩ := Metric.dense_iff.mp (dense_hillReal_open_gap n) (0 : HillRealMeanZeroSource) 1 (by norm_num)
  exact ⟨a.val.val,a.property,a.val.property,ha⟩

theorem exists_hillHminusCanonicalGapSquare_ne_zero (n : ℕ+) :
    ∃ q ∈ hillHminusCanonicalGapDomain, hillHminusCanonicalGapSquare n q ≠ 0 := by
  obtain ⟨q,hr,_,hg⟩ := exists_real_mean_zero_native_gap_ne_zero n
  exact ⟨q,real_mem_hillHminusCanonicalGapDomain q hr,hg⟩

theorem exists_hillHminusCanonicalGapSquare_ne_zero_in_ratioDomain (n : ℕ+) :
    ∃ q ∈ hillHminusCanonicalRatioDomain, hillHminusCanonicalGapSquare n q ≠ 0 := by
  obtain ⟨q,hr,_,hg⟩ := exists_real_mean_zero_native_gap_ne_zero n
  exact ⟨q,real_mem_hillHminusCanonicalRatioDomain q hr,hg⟩

theorem hillHminusCanonicalGapSquare_not_identically_zero (n : ℕ+) :
    ¬∀ q ∈ hillHminusCanonicalRatioDomain, hillHminusCanonicalGapSquare n q=0 := by
  obtain ⟨q,hq,hg⟩ := exists_hillHminusCanonicalGapSquare_ne_zero_in_ratioDomain n
  exact fun hz => hg (hz q hq)

theorem exists_hillHminusCanonicalGapSquare_ne_zero_on_open (n : ℕ+) (U : Set PeriodOneHminusOne)
    (hU : IsOpen U) (hUD : U ⊆ hillHminusCanonicalGapDomain) (hne : U.Nonempty) :
    ∃ q ∈ U, hillHminusCanonicalGapSquare n q ≠ 0 :=
  NLS.ComplexAnalysis.analytic_exists_nonzero_on_nonempty_open
    isConnected_hillHminusCanonicalGapDomain.isPreconnected hU hUD hne
    (hillHminusCanonicalGapSquare n) (analyticOnNhd_hillHminusCanonicalGapSquare n)
    (exists_hillHminusCanonicalGapSquare_ne_zero n)

theorem exists_arbitrarily_near_hillHminusCanonicalGapSquare_ne_zero (n : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ hillHminusCanonicalGapDomain)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ a ∈ hillHminusCanonicalGapDomain, dist a q < epsilon ∧ hillHminusCanonicalGapSquare n a ≠ 0 := by
  obtain ⟨a,ha,hg⟩ := exists_hillHminusCanonicalGapSquare_ne_zero_on_open n
    (hillHminusCanonicalGapDomain ∩ ball q epsilon)
    (isOpen_hillHminusCanonicalGapDomain.inter isOpen_ball) inter_subset_left
    ⟨q,hq,mem_ball_self hepsilon⟩
  exact ⟨a,ha.1,ha.2,hg⟩

end NLS.KdV
