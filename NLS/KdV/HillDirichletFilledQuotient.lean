import NLS.KdV.HillMixedDirichletGardner
import NLS.ComplexAnalysis.MovingCenterDSlope

/-! The ACTUAL Dirichlet characteristic divided by its selected simple
zero, analytically filled at that zero and jointly in the full source. -/
noncomputable section
open Set Complex NLS.ComplexAnalysis
namespace NLS.KdV

def hillHminusDirichletFilledQuotient (n : ℕ+) (t : ℂ × PeriodOneHminusOne) : ℂ :=
  dslope (hillHminusDirichlet t.2) (hillHminusCanonicalDirichlet n t.2) t.1

theorem analyticOnNhd_hillHminusDirichletFilledQuotient (n : ℕ+) :
    AnalyticOnNhd ℂ (hillHminusDirichletFilledQuotient n) (univ ×ˢ hillHminusCanonicalDirichletDomain) :=
  analyticOnNhd_dslope_at_analytic_center
    (fun t : ℂ × PeriodOneHminusOne => hillHminusDirichlet t.2 t.1)
    hillHminusCanonicalDirichletDomain isOpen_hillHminusCanonicalDirichletDomain
    (analyticOnNhd_hillHminusDirichlet_joint.mono (subset_univ _))
    (hillHminusCanonicalDirichlet n) (analyticOnNhd_hillHminusCanonicalDirichlet n)

theorem hillHminusDirichletFilledQuotient_at_root (n : ℕ+) (q : PeriodOneHminusOne) :
    hillHminusDirichletFilledQuotient n (hillHminusCanonicalDirichlet n q,q)=
      deriv (hillHminusDirichlet q) (hillHminusCanonicalDirichlet n q) := dslope_same _ _

theorem hillHminusDirichletFilledQuotient_off_root
    (n : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ hillHminusCanonicalDirichletDomain)
    (E : ℂ) (hE : E ≠ hillHminusCanonicalDirichlet n q) :
    hillHminusDirichletFilledQuotient n (E,q)=hillHminusDirichlet q E/(E-hillHminusCanonicalDirichlet n q) := by
  rw [hillHminusDirichletFilledQuotient,dslope_of_ne _ hE,slope_def_field,
    hillHminusCanonicalDirichlet_is_root n q hq,sub_zero]

theorem hillHminusDirichletFilledQuotient_factor
    (n : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ hillHminusCanonicalDirichletDomain) (E : ℂ) :
    (E-hillHminusCanonicalDirichlet n q)*hillHminusDirichletFilledQuotient n (E,q)=hillHminusDirichlet q E := by
  by_cases hE : E=hillHminusCanonicalDirichlet n q
  · rw [hE,sub_self,zero_mul,hillHminusCanonicalDirichlet_is_root n q hq]
  · rw [hillHminusDirichletFilledQuotient_off_root n q hq E hE]
    field_simp

end NLS.KdV
