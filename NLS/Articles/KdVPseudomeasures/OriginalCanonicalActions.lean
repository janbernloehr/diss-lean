import NLS.Articles.KdVPseudomeasures.OriginalMiuraAllIndices
import NLS.KdV.HillHminusOneCanonicalActions

/-! # Canonical actions on the entire original physical H-minus-one domain

One common connected OPEN COMPLEX neighborhood contains every original
real mean-zero period-one H-minus-one potential and supports ALL indexed
analytic actions. On the full original real domain they are the literal
two-over-pi Hill arcosh gap integrals, independent of every Miura choice,
real and nonnegative, and zero exactly at the original collapsed gap.
No endpoint-space membership or Birkhoff-map assumption is used.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV

def originalCanonicalHillAction (n : ℕ+) (q : OriginalHminusOnePotential) : ℂ :=
  hillHminusCanonicalAction n (originalPeriodOneCoefficients q)

theorem originalCanonicalHillAction_eq_real_gapIntegral
    (q : OriginalHminusOnePotential) (n : ℕ+) :
    originalCanonicalHillAction n q =
      ((2/Real.pi * ∫ E in originalHillLabels q (2*(n : ℕ)-1)..originalHillLabels q (2*(n : ℕ)),
        Real.arcosh ((if ((n : ℕ) : ℤ)%2 = 0 then (originalHillDiscriminant q E).re
          else -(originalHillDiscriminant q E).re)/2) : ℝ) : ℂ) := by
  unfold originalCanonicalHillAction
  rw [hillHminusCanonicalAction_eq_real _ (originalPeriodOneCoefficients_real q)]
  rfl

theorem originalCanonicalHillAction_eq_Miura
    (q : OriginalHminusOnePotential) (u : PeriodOneRealL2) (c : ℝ)
    (himage : periodOneMiura u.val = originalPeriodOneCoefficients q+
      periodOneL2Inclusion (lp.single 2 0 (c : ℂ)))
    (hc : -(c : ℂ) ∉ singularHillSpectrum q.val) (n : ℕ+) :
    originalCanonicalHillAction n q = hillHminusMiuraIndexedAction u.val (n : ℕ) := by
  apply hillHminusCanonicalAction_eq_Miura_of_real (originalPeriodOneCoefficients q)
    (originalPeriodOneCoefficients_real q) u c himage
  simpa only [periodOneOriginal_originalPeriodOneCoefficients] using hc

theorem originalCanonicalHillAction_properties (q : OriginalHminusOnePotential) (n : ℕ+) :
    0 ≤ (originalCanonicalHillAction n q).re ∧ (originalCanonicalHillAction n q).im = 0 ∧
      (originalCanonicalHillAction n q = 0 ↔ originalCanonicalGapValues q (n : ℕ) = 0) := by
  have h := hillHminusCanonicalAction_real_properties (originalPeriodOneCoefficients q)
    (originalPeriodOneCoefficients_real q) n
  have hn : ((n : ℕ) : ℤ) ≠ 0 := by exact_mod_cast n.ne_zero
  simpa only [originalCanonicalHillAction,originalCanonicalGapValues,if_neg hn,
    Int.natAbs_natCast,originalHillLabels] using h

theorem originalCanonicalHillAction_pos_iff_gap_ne_zero (q : OriginalHminusOnePotential) (n : ℕ+) :
    0 < (originalCanonicalHillAction n q).re ↔ originalCanonicalGapValues q (n : ℕ) ≠ 0 := by
  have hs := originalCanonicalHillAction_properties q n
  constructor
  · intro h hgap
    rw [hs.2.2.mpr hgap,zero_re] at h
    exact lt_irrefl 0 h
  · intro hgap
    have hne : originalCanonicalHillAction n q ≠ 0 := fun h => hgap (hs.2.2.mp h)
    apply lt_of_le_of_ne hs.1
    intro he
    exact hne (Complex.ext he.symm hs.2.1)

theorem exists_common_complex_neighborhood_originalCanonicalHillActions :
    ∃ W : Set PeriodOneHminusOne, IsOpen W ∧ IsConnected W ∧
      (∀ q : OriginalHminusOnePotential, originalPeriodOneCoefficients q ∈ W) ∧
      ∀ n : ℕ+, AnalyticOnNhd ℂ (hillHminusCanonicalAction n) W := by
  exact ⟨hillHminusCanonicalActionDomain,isOpen_hillHminusCanonicalActionDomain,
    isConnected_hillHminusCanonicalActionDomain,
    fun q => real_mem_hillHminusCanonicalActionDomain _ (originalPeriodOneCoefficients_real q),
    analyticOnNhd_hillHminusCanonicalAction⟩

end NLS.Articles.KdVPseudomeasures
