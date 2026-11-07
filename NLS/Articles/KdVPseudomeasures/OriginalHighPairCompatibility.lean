import NLS.Articles.KdVPseudomeasures.PeriodicSourceCircles
import NLS.KdV.HillHminusHighPairStrip
import NLS.KdV.HillHminusOneActionRatio
import NLS.ComplexAnalysis.UnorderedPairSupport

/-! The actual high pairs used by the original endpoint estimates and
by the native analytic formulas agree as UNORDERED pairs, even at complex
collapse. Literal physical distribution and positive indices are retained. -/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue NLS.ComplexAnalysis

def sourceNativePeriodOneCLM (r : ℝ) (hr : AdmissiblePredualOrder r) :
    FourierLebesgueSpace (2:ℝ) (-r) ⊤ →L[ℂ] PeriodOneHminusOne :=
  periodOneOriginalExtract.comp (endpointLowerInclusion (-r) (-1) (by norm_num) (admissible_hminusOne_threshold r hr))

theorem sourceNativePeriodOneCLM_apply (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) :
    sourceNativePeriodOneCLM r hr q=periodOneOriginalExtract (sourceComplexHminusOne r hr q) := rfl

theorem sourceNativePeriodOneCLM_distribution (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (hp : IsPeriodicDistribution 1 q.val.toTempered) :
    periodOneOriginal (sourceNativePeriodOneCLM r hr q)=sourceComplexHminusOne r hr q :=
  originalComplexDirichlet_distribution (sourceOriginalComplexPotential r hr q hp)

theorem sourceNativePeriodOne_spectral_iff (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (hp : IsPeriodicDistribution 1 q.val.toTempered) (z : ℂ) :
    z ∈ sourceHillSpectrum r hr q ↔ hillHminusRadicand (sourceNativePeriodOneCLM r hr q) z=0 := by
  change z ∈ singularHillSpectrum (sourceComplexHminusOne r hr q) ↔ _
  rw [← sourceNativePeriodOneCLM_distribution r hr q hp,
    singularHillSpectrum_periodOne_iff_discriminant]
  exact sub_eq_zero.symm

theorem SourceHillComplexPair.eq_or_swap_native_high_pair
    (r : ℝ) (hr : AdmissiblePredualOrder r) (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤)
    (hp : IsPeriodicDistribution 1 q.val.toTempered) (n : ℕ+) (p : SourceHillComplexPair r hr q (n:ℕ))
    (rho : ℝ) (hrho : rho ≤ Real.pi/4) (l u : ℂ)
    (hpair : HillHminusHighGapPair (sourceNativePeriodOneCLM r hr q) n rho l u)
    (hlocal : Real.sqrt (n:ℝ)/4 < Real.pi*(n:ℝ)*rho) :
    (l=p.left ∧ u=p.right) ∨ (l=p.right ∧ u=p.left) := by
  have hstrip := hillHminusGapSquareDisc_subset_reducedHillStrip n rho hrho
  have hl := (p.spectrum_iff r hr q (n:ℕ) l (hstrip (ball_subset_closedBall hpair.left_mem))).mp
    ((sourceNativePeriodOne_spectral_iff r hr q hp l).mpr hpair.left_zero)
  have hu := (p.spectrum_iff r hr q (n:ℕ) u (hstrip (ball_subset_closedBall hpair.right_mem))).mp
    ((sourceNativePeriodOne_spectral_iff r hr q hp u).mpr hpair.right_zero)
  have hleft : p.left ∈ hillHminusGapSquareDisc n rho := by
    apply ball_subset_closedBall
    rw [mem_ball,dist_eq_norm]
    rw [← freeHillValue_natCast_complex]
    exact p.left_localized.trans_lt hlocal
  have hright : p.right ∈ hillHminusGapSquareDisc n rho := by
    apply ball_subset_closedBall
    rw [mem_ball,dist_eq_norm]
    rw [← freeHillValue_natCast_complex]
    exact p.right_localized.trans_lt hlocal
  have ha := (hpair.zeros_iff p.left hleft).mp
    ((sourceNativePeriodOne_spectral_iff r hr q hp p.left).mp (by
      rw [sourceHillSpectrum_eq];exact p.left_spectral))
  have hb := (hpair.zeros_iff p.right hright).mp
    ((sourceNativePeriodOne_spectral_iff r hr q hp p.right).mp (by
      rw [sourceHillSpectrum_eq];exact p.right_spectral))
  exact eq_or_swap_of_pair_support l u p.left p.right hl hu ha hb

theorem SourceHillComplexPair.native_high_midpoint_and_gap
    (r : ℝ) (hr : AdmissiblePredualOrder r) (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤)
    (hp : IsPeriodicDistribution 1 q.val.toTempered) (n : ℕ+) (p : SourceHillComplexPair r hr q (n:ℕ))
    (rho : ℝ) (hrhop : 0 < rho) (hrho : rho ≤ Real.pi/4) (l u : ℂ)
    (hpair : HillHminusHighGapPair (sourceNativePeriodOneCLM r hr q) n rho l u)
    (hlocal : Real.sqrt (n:ℝ)/4 < Real.pi*(n:ℝ)*rho) :
    hillHminusGapMidpoint n rho (sourceNativePeriodOneCLM r hr q)=(p.left+p.right)/2 ∧
      4*hillHminusSquaredHalfGap n rho (sourceNativePeriodOneCLM r hr q)=(p.right-p.left)^2 := by
  have he := hpair.symmetric_gap_data hrhop
  rw [he.1,he.2]
  rcases p.eq_or_swap_native_high_pair r hr q hp n rho hrho l u hpair hlocal with h | h <;>
    rw [h.1,h.2] <;> constructor <;> ring

end NLS.Articles.KdVPseudomeasures
