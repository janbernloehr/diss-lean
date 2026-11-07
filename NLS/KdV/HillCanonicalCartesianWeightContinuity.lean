import NLS.KdV.HillCanonicalCartesianWeight

/-! The intrinsic energy weight is continuous near every real potential,
including closed gaps and Dirichlet endpoints. -/
noncomputable section
namespace NLS.KdV

theorem continuousAt_hillHminusCanonicalCartesianWeight_real (n : ℕ+)
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) :
    ContinuousAt (hillHminusCanonicalCartesianWeight n) q := by
  have hg := (analyticOnNhd_hillHminusCanonicalGapSquare n q
    (real_mem_hillHminusCanonicalGapDomain q hr)).continuousAt
  have hd := (analyticOnNhd_hillHminusCanonicalDirichlet n q
    (real_mem_hillHminusCanonicalDirichletDomain q hr)).continuousAt
  have hm := (analyticOnNhd_hillHminusCanonicalEnergyMidpoint n q
    (real_mem_hillHminusCanonicalZeroSequenceDomain q hr)).continuousAt
  exact (Real.continuous_sqrt.continuousAt.comp hg.norm).add (hd.sub hm).norm

end NLS.KdV
