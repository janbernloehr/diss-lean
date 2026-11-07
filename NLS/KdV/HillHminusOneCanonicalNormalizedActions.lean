import NLS.KdV.HillHminusOneNormalizedActionBalls
import NLS.ComplexAnalysis.AnalyticScalarFactorUniqueness

/-! # Nonzero analytic canonical action ratios at ALL positive indices

The analytic scalar identity principle glues the actual local quotients
across collapsed gaps. If a squared gap were identically zero on the
entire common connected domain, the constant1 is a valid nonzero filled
quotient for that index. Otherwise analytic cancellation proves agreement
on every overlap. This handles the degenerate alternative without an
unproved generic-open-gap or density assertion.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped Classical
namespace NLS.KdV

theorem analyticOnNhd_hillHminusCanonicalGapSquare_on_ratioDomain (n : ℕ+) :
    AnalyticOnNhd ℂ (hillHminusCanonicalGapSquare n) hillHminusCanonicalRatioDomain :=
  (analyticOnNhd_hillHminusCanonicalGapSquare n).mono hillHminusCanonicalRatioDomain_subset

theorem analyticOnNhd_hillHminusCanonicalAction_on_ratioDomain (n : ℕ+) :
    AnalyticOnNhd ℂ (hillHminusCanonicalAction n) hillHminusCanonicalRatioDomain :=
  (analyticOnNhd_hillHminusCanonicalAction_on_gapDomain n).mono hillHminusCanonicalRatioDomain_subset

theorem HillHminusNormalizedActionBall.ratio_eq_on_overlap
    (B C : HillHminusNormalizedActionBall) (n : ℕ+)
    (hne : ∃ a ∈ hillHminusCanonicalRatioDomain, hillHminusCanonicalGapSquare n a ≠ 0) :
    EqOn (B.ratio n) (C.ratio n) (B.source ∩ C.source) := by
  have hK : (8*((Real.pi : ℂ)*(n : ℕ))) ≠ 0 :=
    mul_ne_zero (by norm_num) (mul_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero) (by exact_mod_cast n.ne_zero))
  have hf : AnalyticOnNhd ℂ (fun a => hillHminusCanonicalGapSquare n a/(8*((Real.pi : ℂ)*(n : ℕ))))
      hillHminusCanonicalRatioDomain := fun a ha =>
    (analyticOnNhd_hillHminusCanonicalGapSquare_on_ratioDomain n a ha).div_const
  obtain ⟨a,ha,hga⟩ := hne
  exact analytic_eqOn_of_mul_eq_mul_on_open isConnected_hillHminusCanonicalRatioDomain.isPreconnected
    (B.source_open.inter C.source_open) (fun x hx => mem_iUnion.mpr ⟨B,hx.1⟩) _ _ _ hf
    ((B.ratio_analytic n).mono inter_subset_left) ((C.ratio_analytic n).mono inter_subset_right)
    ⟨a,ha,div_ne_zero hga hK⟩ (fun x hx => (B.factor n x hx.1).symm.trans (C.factor n x hx.2))

def hillHminusCanonicalActionRatio (n : ℕ+) (q : PeriodOneHminusOne) : ℂ :=
  if ∀ a ∈ hillHminusCanonicalRatioDomain, hillHminusCanonicalGapSquare n a = 0 then 1
  else if hq : q ∈ hillHminusCanonicalRatioDomain then
    (Classical.choose (mem_iUnion.mp hq)).ratio n q
  else 1

theorem HillHminusNormalizedActionBall.canonical_ratio_eq
    (B : HillHminusNormalizedActionBall) (n : ℕ+)
    (hne : ∃ a ∈ hillHminusCanonicalRatioDomain, hillHminusCanonicalGapSquare n a ≠ 0)
    (q : PeriodOneHminusOne) (hq : q ∈ B.source) :
    hillHminusCanonicalActionRatio n q = B.ratio n q := by
  have hdom : q ∈ hillHminusCanonicalRatioDomain := mem_iUnion.mpr ⟨B,hq⟩
  have hn : ¬ ∀ a ∈ hillHminusCanonicalRatioDomain, hillHminusCanonicalGapSquare n a = 0 := by
    obtain ⟨a,ha,hga⟩ := hne
    exact fun h => hga (h a ha)
  rw [hillHminusCanonicalActionRatio,if_neg hn,dif_pos hdom]
  let C : HillHminusNormalizedActionBall := Classical.choose (mem_iUnion.mp hdom)
  have hC : q ∈ C.source := Classical.choose_spec (mem_iUnion.mp hdom)
  exact C.ratio_eq_on_overlap B n hne ⟨hC,hq⟩

theorem analyticOnNhd_hillHminusCanonicalActionRatio (n : ℕ+) :
    AnalyticOnNhd ℂ (hillHminusCanonicalActionRatio n) hillHminusCanonicalRatioDomain := by
  by_cases hz : ∀ a ∈ hillHminusCanonicalRatioDomain, hillHminusCanonicalGapSquare n a = 0
  · have he : hillHminusCanonicalActionRatio n = fun _ => (1 : ℂ) := by
      funext q
      rw [hillHminusCanonicalActionRatio,if_pos hz]
    rw [he]
    exact analyticOnNhd_const
  · have hne : ∃ a ∈ hillHminusCanonicalRatioDomain, hillHminusCanonicalGapSquare n a ≠ 0 := by simpa using hz
    intro q hq
    obtain ⟨B,hB⟩ := mem_iUnion.mp hq
    apply (B.ratio_analytic n q hB).congr
    filter_upwards [B.source_open.mem_nhds hB] with a ha
    exact (B.canonical_ratio_eq n hne a ha).symm

theorem hillHminusCanonicalActionRatio_ne_zero (n : ℕ+) (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusCanonicalRatioDomain) : hillHminusCanonicalActionRatio n q ≠ 0 := by
  by_cases hz : ∀ a ∈ hillHminusCanonicalRatioDomain, hillHminusCanonicalGapSquare n a = 0
  · simp only [hillHminusCanonicalActionRatio,if_pos hz,ne_eq,one_ne_zero,not_false_eq_true]
  · have hne : ∃ a ∈ hillHminusCanonicalRatioDomain, hillHminusCanonicalGapSquare n a ≠ 0 := by simpa using hz
    obtain ⟨B,hB⟩ := mem_iUnion.mp hq
    rw [B.canonical_ratio_eq n hne q hB]
    exact B.ratio_nonzero n q hB

theorem hillHminusCanonicalAction_gap_factorization (n : ℕ+) (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusCanonicalRatioDomain) :
    hillHminusCanonicalAction n q = hillHminusCanonicalGapSquare n q /
      (8*((Real.pi : ℂ)*(n : ℕ)))*hillHminusCanonicalActionRatio n q := by
  by_cases hz : ∀ a ∈ hillHminusCanonicalRatioDomain, hillHminusCanonicalGapSquare n a = 0
  · have hI := (hillHminusCanonicalAction_eq_zero_iff_gapSquare n q hq).mpr (hz q hq)
    rw [hI,hz q hq,zero_div,zero_mul]
  · have hne : ∃ a ∈ hillHminusCanonicalRatioDomain, hillHminusCanonicalGapSquare n a ≠ 0 := by simpa using hz
    obtain ⟨B,hB⟩ := mem_iUnion.mp hq
    rw [B.canonical_ratio_eq n hne q hB]
    exact B.factor n q hB

theorem hillHminusCanonicalActionRatio_eq_quotient (n : ℕ+) (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusCanonicalRatioDomain) (hg : hillHminusCanonicalGapSquare n q ≠ 0) :
    hillHminusCanonicalActionRatio n q =
      (8*((Real.pi : ℂ)*(n : ℕ)))*hillHminusCanonicalAction n q/hillHminusCanonicalGapSquare n q := by
  have hK : (8*((Real.pi : ℂ)*(n : ℕ))) ≠ 0 :=
    mul_ne_zero (by norm_num) (mul_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero) (by exact_mod_cast n.ne_zero))
  rw [hillHminusCanonicalAction_gap_factorization n q hq]
  field_simp [hg,hK]

theorem hillHminusCanonicalActionRatio_unique_on_open
    (n : ℕ+) (U : Set PeriodOneHminusOne) (hU : IsOpen U) (hUD : U ⊆ hillHminusCanonicalRatioDomain)
    (R : PeriodOneHminusOne → ℂ) (hR : AnalyticOnNhd ℂ R U)
    (hne : ∃ a ∈ hillHminusCanonicalRatioDomain, hillHminusCanonicalGapSquare n a ≠ 0)
    (hfactor : ∀ a ∈ U, hillHminusCanonicalAction n a =
      hillHminusCanonicalGapSquare n a/(8*((Real.pi : ℂ)*(n : ℕ)))*R a) :
    EqOn (hillHminusCanonicalActionRatio n) R U := by
  have hK : (8*((Real.pi : ℂ)*(n : ℕ))) ≠ 0 :=
    mul_ne_zero (by norm_num) (mul_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero) (by exact_mod_cast n.ne_zero))
  obtain ⟨a,ha,hga⟩ := hne
  apply analytic_eqOn_of_mul_eq_mul_on_open isConnected_hillHminusCanonicalRatioDomain.isPreconnected hU hUD
    (fun a => hillHminusCanonicalGapSquare n a/(8*((Real.pi : ℂ)*(n : ℕ)))) _ _
    (fun a ha => (analyticOnNhd_hillHminusCanonicalGapSquare_on_ratioDomain n a ha).div_const)
    ((analyticOnNhd_hillHminusCanonicalActionRatio n).mono hUD) hR ⟨a,ha,div_ne_zero hga hK⟩
  intro b hb
  exact (hillHminusCanonicalAction_gap_factorization n b (hUD hb)).symm.trans (hfactor b hb)

end NLS.KdV
