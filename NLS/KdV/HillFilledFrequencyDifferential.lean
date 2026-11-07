import NLS.KdV.HillAbelianOddGapNumerator
import NLS.KdV.HillAbelianJointFrequencyDomain
import NLS.ZakharovShabat.SourceOpenGapReflection
import NLS.ZakharovShabat.SourceRealPsiFilledQuotient

/-! The actual Hill frequency differential filled at collapsed Dirac
gaps. Its exact evenness and spectral analyticity retain the original
canonical numerator and product root. -/
noncomputable section
open Set Complex NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

def filledAbelianFrequencyDifferential (P : HillProductEquationPatch) (n : ℕ+)
    (t : ℂ × PeriodOneHminusOne) : ℂ :=
  sourcePsiFilledQuotient (by simp) (by norm_num) (n:ℤ)
    (P.parent.family.roots (n:ℤ) (P.sourcePsi t.2)) (P.sourcePsi t.2) t.1+
  sourcePsiFilledQuotient (by simp) (by norm_num) (n:ℤ)
    (P.parent.family.roots (n:ℤ) (P.sourcePsi t.2)) (P.sourcePsi t.2) (-t.1)

theorem filledAbelianFrequencyDifferential_neg (P : HillProductEquationPatch) (n : ℕ+)
    (z : ℂ) (q : PeriodOneHminusOne) :
    P.filledAbelianFrequencyDifferential n (-z,q)=P.filledAbelianFrequencyDifferential n (z,q) := by
  simp only [filledAbelianFrequencyDifferential,neg_neg,add_comm]

theorem filledAbelianFrequencyDifferential_eq_actual (P : HillProductEquationPatch) (n : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (z : ℂ)
    (hz : z ∈ sourceCanonicalRootDomain (by simp) (by norm_num) (P.sourcePsi q)) :
    P.filledAbelianFrequencyDifferential n (z,q)=P.abelianFrequencyDifferential n (z,q) := by
  have h : SourcePeriodicReflection (by simp) (by norm_num) (P.sourcePsi q) :=
    sourcePeriodicReflection_hillMiuraDiagonal (P.parent.parent.miuraBall.actionBall.lift q)
  have hneg := (h.neg_mem_rootDomain_iff z).mpr hz
  dsimp only [filledAbelianFrequencyDifferential]
  rw [
    sourcePsiFilledQuotient_eq_contourIntegrand (by simp) (by norm_num) (n:ℤ) _ _ z hz,
    sourcePsiFilledQuotient_eq_contourIntegrand (by simp) (by norm_num) (n:ℤ) _ _ (-z) hneg]
  simp only [sourcePsiContourIntegrandJoint]
  rw [abelianFrequencyDifferential,P.abelianFrequencyNumerator_eq_odd_selected n q hq z,
    h.canonicalRoot_neg z,div_neg]
  dsimp only
  ring

theorem analytic_filledAbelianFrequencyDifferential (P : HillProductEquationPatch) (n : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q)
    (hn : canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential (P.sourcePsi q))
      (periodOnePotential_mem _) (n:ℤ) ≠ 0) :
    AnalyticOnNhd ℂ (fun z => P.filledAbelianFrequencyDifferential n (z,q))
      (sourceOpenGapComplement (by simp) (by norm_num) (P.sourcePsi q)) := by
  let u : PeriodOneRealL2 := ⟨P.parent.parent.miuraBall.actionBall.lift q,
    P.parent.parent.miuraBall.actionBall.lift_real q (P.parent.subset (P.subset hq)).1 hr⟩
  let φ : realTypeSourceLocus 2 := hillMiuraRealSource u
  have ha := sourcePsiFilledQuotient_analytic_real (by simp) (by norm_num) φ (n:ℤ) hn
  have he := P.parent.family.verified.real_agreement (n:ℤ) φ
  rw [← he] at ha
  intro z hz
  have h := sourcePeriodicReflection_hillMiuraDiagonal u.val
  exact (ha z hz).add ((ha (-z) ((h.neg_mem_openGapComplement_iff z).mpr hz)).comp
    (f := fun w : ℂ => -w) analyticAt_id.neg)

end NLS.KdV.HillProductEquationPatch
