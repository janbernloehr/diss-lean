import NLS.ComplexAnalysis.CoshRealBranch
import NLS.KdV.HillHminusOneRealGapProfile
import NLS.KdV.HillHminusOneValidGapBoundary
import NLS.KdV.HillHminusOneCanonicalActions
import NLS.KdV.HillHminusOneGluedHighActions

/-! # Canonical actions agree with actual high charts at the SAME original index

The continuous principal square root is fixed by its nonnegative real
part, exact cosh value and zero endpoint. This identifies its whole real
gap profile with the actual arcosh profile. The two-over-pi area and the
previous intrinsic ratio formula then give equality with the canonical
action, including collapse. The original label hypothesis is explicit.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex MeasureTheory NLS.ComplexAnalysis
namespace NLS.KdV

theorem HillHminusActionChartValid.sqrt_eq_canonical_profile
    {q : PeriodOneHminusOne} {n : ℕ+} {r : ℝ} {K : ℂ × PeriodOneHminusOne → ℂ}
    (h : HillHminusActionChartValid n r K q) (hq : IsRealPeriodOneHminusOne q)
    (l u : ℝ) (hpair : HillHminusHighGapPair q n r (l : ℂ) (u : ℂ))
    (hl : l = hillHminusLabels q hq (2*(n : ℕ)-1))
    (hu : u = hillHminusLabels q hq (2*(n : ℕ))) :
    EqOn (fun E : ℝ => Complex.sqrt (K ((E : ℂ),q)))
      (fun E => (hillHminusRealGapProfile q (n : ℕ) E : ℂ)) (Icc l u) := by
  have hlu : l ≤ u := by
    rw [hl,hu]
    exact monotone_hillHminusLabels q hq (by omega)
  have hp := hillHminusRealGapProfile_canonical_gap_spec q hq n
  dsimp only at hp
  rw [← hl,← hu] at hp
  have hzero : K ((l : ℂ),q) = 0 := by
    have hf := h.real_gap_factorization l u hpair l ⟨le_rfl,hlu⟩
    simpa only [sub_self,neg_zero,zero_mul,zero_div] using hf
  apply continuous_cosh_real_branch_eqOn (fun E : ℝ => Complex.sqrt (K ((E : ℂ),q)))
    (hillHminusRealGapProfile q (n : ℕ)) (Icc l u) isPreconnected_Icc
    (h.real_gap_sqrt_continuousOn l u hpair) hp.1
    (fun E _ => re_sqrt_nonneg _) (fun E hE => (hp.2.2.2 E hE).1) ?_
    l ⟨le_rfl,hlu⟩ ?_
  · intro E hE
    exact (h.2.2.2.1 (E : ℂ) (hpair.real_gap_mem_ball E hE)).trans (hp.2.2.2 E hE).2.symm
  · rw [hzero,Complex.sqrt_zero,hp.2.1,ofReal_zero]

theorem HillHminusActionChartValid.boundary_action_eq_canonical
    {q : PeriodOneHminusOne} {n : ℕ+} {r : ℝ} {K : ℂ × PeriodOneHminusOne → ℂ}
    (h : HillHminusActionChartValid n r K q) (hq : IsRealPeriodOneHminusOne q)
    (l u : ℝ) (hpair : HillHminusHighGapPair q n r (l : ℂ) (u : ℂ))
    (hl : l = hillHminusLabels q hq (2*(n : ℕ)-1))
    (hu : u = hillHminusLabels q hq (2*(n : ℕ))) :
    hillHminusGapBoundaryAction K q l u = hillHminusCanonicalAction n q := by
  have hlu : l ≤ u := by rw [hl,hu]; exact monotone_hillHminusLabels q hq (by omega)
  have hi : (∫ E in l..u, Complex.sqrt (K ((E : ℂ),q))) =
      ∫ E in l..u, (hillHminusRealGapProfile q (n : ℕ) E : ℂ) := by
    apply intervalIntegral.integral_congr
    intro E hE
    exact h.sqrt_eq_canonical_profile hq l u hpair hl hu (by simpa only [uIcc_of_le hlu] using hE)
  rw [hillHminusCanonicalAction_eq_real q hq n]
  unfold hillHminusGapBoundaryAction hillHminusCanonicalRealAction
  rw [← hl,← hu,hi,intervalIntegral.integral_ofReal]
  push_cast
  rfl

theorem HillHminusActionChartValid.canonical_action_eq_gap_ratio
    {q : PeriodOneHminusOne} {n : ℕ+} {r : ℝ} {K : ℂ × PeriodOneHminusOne → ℂ}
    (h : HillHminusActionChartValid n r K q) (hq : IsRealPeriodOneHminusOne q)
    (l u : ℝ) (hpair : HillHminusHighGapPair q n r (l : ℂ) (u : ℂ))
    (hl : l = hillHminusLabels q hq (2*(n : ℕ)-1))
    (hu : u = hillHminusLabels q hq (2*(n : ℕ))) :
    hillHminusCanonicalAction n q =
      (((u-l : ℝ) : ℂ)^2/(8*((Real.pi : ℂ)*(n : ℕ))))*hillHminusNormalizedActionRatio n r K q := by
  have hlu : l ≤ u := by rw [hl,hu]; exact monotone_hillHminusLabels q hq (by omega)
  exact (h.boundary_action_eq_canonical hq l u hpair hl hu).symm.trans
    (h.boundary_action_eq_ratio l u hlu hpair)

theorem HillHminusActionNeighborhood.glued_action_eq_canonical_of_real_labels
    {n : ℕ+} {r : ℝ} {K : ℂ × PeriodOneHminusOne → ℂ} {V : Set PeriodOneHminusOne}
    (h : HillHminusActionNeighborhood n r K V) (q : PeriodOneHminusOne) (hqV : q ∈ V)
    (hq : IsRealPeriodOneHminusOne q) (l u : ℝ)
    (hpair : HillHminusHighGapPair q n r (l : ℂ) (u : ℂ))
    (hl : l = hillHminusLabels q hq (2*(n : ℕ)-1))
    (hu : u = hillHminusLabels q hq (2*(n : ℕ))) :
    hillHminusGluedHighAction n q = hillHminusCanonicalAction n q := by
  rw [hillHminusGluedHighAction,h.glued_gap_square_eq_pair hqV (l : ℂ) (u : ℂ) hpair,h.glued_ratio_eq hqV]
  simpa only [ofReal_sub] using ((h.valid hqV).canonical_action_eq_gap_ratio hq l u hpair hl hu).symm

end NLS.KdV
