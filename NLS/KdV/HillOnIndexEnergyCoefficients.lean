import NLS.KdV.HillOnIndexBranchCoefficients
import NLS.KdV.HillAbelianEnergyQuotient

/-! ACTUAL diagonal Cartesian coefficients in ORIGINAL Hill energy.
Both are jointly analytic through the entire gap and its branch points.
At the actual physical Dirichlet energy, the two Cartesian factors are
A plus/minus the ACTUAL norming sheet times B. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

def onIndexEnergyEven (P : HillProductEquationPatch) (n : ℕ+) (t : ℂ × PeriodOneHminusOne) : ℂ :=
  P.onIndexFrequencyEven n (P.abelianEnergyCoordinates t)

def onIndexEnergyOdd (P : HillProductEquationPatch) (n : ℕ+) (t : ℂ × PeriodOneHminusOne) : ℂ :=
  P.onIndexFrequencyOdd n (P.abelianEnergyCoordinates t)

theorem analytic_onIndexEnergyEven (P : HillProductEquationPatch) (n : ℕ+) :
    AnalyticOnNhd ℂ (P.onIndexEnergyEven n) (P.abelianFilledEnergyDomain n) := by
  intro t ht
  exact (P.analytic_onIndexFrequencyEven n _ ht.2).comp (f := P.abelianEnergyCoordinates)
    (P.analytic_abelianEnergyCoordinates t ht.1)

theorem analytic_onIndexEnergyOdd (P : HillProductEquationPatch) (n : ℕ+) :
    AnalyticOnNhd ℂ (P.onIndexEnergyOdd n) (P.abelianFilledEnergyDomain n) := by
  intro t ht
  exact (P.analytic_onIndexFrequencyOdd n _ ht.2).comp (f := P.abelianEnergyCoordinates)
    (P.analytic_abelianEnergyCoordinates t ht.1)

theorem onIndexEnergyCoefficients_at_positive_frequency (P : HillProductEquationPatch) (n : ℕ+)
    (q : PeriodOneHminusOne) (z : ℂ) (hz : 0 < z.re) :
    P.onIndexEnergyEven n (z^2-(P.parent.parent.miuraBall.actionBall.shift:ℂ),q) = P.onIndexFrequencyEven n (z,q) ∧
    P.onIndexEnergyOdd n (z^2-(P.parent.parent.miuraBall.actionBall.shift:ℂ),q) = P.onIndexFrequencyOdd n (z,q) := by
  simp only [onIndexEnergyEven,onIndexEnergyOdd,abelianEnergyCoordinates,sub_add_cancel,sqrt_sq_of_re_pos z hz,and_self]

theorem physicalOnIndexCartesian_eq_original_energy_coefficients_of_real (P : HillProductEquationPatch) (n : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) :
    P.physicalOnIndexCartesianPlus n q = P.onIndexEnergyEven n (hillHminusCanonicalDirichlet n q,q)+
      hillHminusDirichletSheet n q*P.onIndexEnergyOdd n (hillHminusCanonicalDirichlet n q,q) ∧
    P.physicalOnIndexCartesianMinus n q = P.onIndexEnergyEven n (hillHminusCanonicalDirichlet n q,q)-
      hillHminusDirichletSheet n q*P.onIndexEnergyOdd n (hillHminusCanonicalDirichlet n q,q) := by
  have hqd := P.real_mem_physicalDirichletSource q hq hr
  have hz := P.abelianGapDisc_re_pos_of_real n q hq hr _ (P.physicalDirichletFrequency_mem_disc q hqd ((n:ℕ):ℤ))
  have hc := P.onIndexEnergyCoefficients_at_positive_frequency n q _ hz
  rw [P.physicalDirichletFrequency_energy n q hq] at hc
  rw [hc.1,hc.2]
  exact P.physicalOnIndexCartesian_eq_frequency_coefficients n q hqd

theorem onIndexEnergyEven_at_original_left_endpoint (P : HillProductEquationPatch) (n : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) :
    P.onIndexEnergyEven n ((hillHminusLabels q hr (2*(n:ℕ)-1):ℂ),q) =
      ((hillHminusLabels q hr (2*(n:ℕ))-hillHminusLabels q hr (2*(n:ℕ)-1):ℝ):ℂ) := by
  let l := canonicalPeriodicLeft (by norm_num) (by norm_num) (periodOnePotential (P.sourcePsi q)) (periodOnePotential_mem _) ((n:ℕ):ℤ)
  let τ := sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((n:ℕ):ℤ)
  have hlD : l ∈ ball (P.centers ((n:ℕ):ℤ):ℂ) (P.radii ((n:ℕ):ℤ)) := by
    rw [← P.discs_eq]
    exact P.isolating.gap (P.sourcePsi q) (P.image q hq).2 _ (left_mem_segment ℝ _ _)
  have hlpos := P.abelianGapDisc_re_pos_of_real n q hq hr l hlD
  have he := P.onIndexEnergyCoefficients_at_positive_frequency n q l hlpos
  rw [(P.abelian_gap_endpoint_energies_eq_original_labels n q hq hr).1] at he
  rw [he.1]
  have hQ : (P.onIndexBranchCoordinates n (l,q)).1 = 0 := by
    change sourceAngularSelectedPolynomial (by norm_num) (by norm_num) (P.sourcePsi q) ((n:ℕ):ℤ) l = 0
    rw [sourceAngularSelectedPolynomial_eq_endpoint_factor]
    change (l-l)*_ = 0
    rw [sub_self,zero_mul]
  have hC : rootPhaseEven (P.onIndexBranchCoordinates n (l,q)) = 1 := by
    change rootPhaseEven ((P.onIndexBranchCoordinates n (l,q)).1,(P.onIndexBranchCoordinates n (l,q)).2) = 1
    rw [hQ]
    exact rootPhaseEven_zero _
  rw [← P.original_energy_gap_eq_four_midpoint_halfgap_of_real n q hq hr]
  unfold onIndexFrequencyEven
  change -4*τ*((l-τ)*rootPhaseEven (P.onIndexBranchCoordinates n (l,q))-
    (P.onIndexBranchCoordinates n (l,q)).1*rootPhaseOdd (P.onIndexBranchCoordinates n (l,q))) = _
  rw [hC,hQ,mul_one,zero_mul,sub_zero]
  dsimp only [τ,l,sourceStandardRootMidpoint,sourceStandardRootHalfGap,canonicalPeriodicMidpoint,canonicalPeriodicGap]
  ring

end NLS.KdV.HillProductEquationPatch
