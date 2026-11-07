import NLS.KdV.HillDirichletNormingGardner
import NLS.ComplexAnalysis.NormalizedLogChart

/-! Actual local logarithmic norming coordinates with normalization
-2*log(rho/rho_base). They are analytic near every complex base source,
including closed gaps, and have the exact Dirichlet cross bracket one.
No multiplier/multiplier or logarithm/logarithm bracket is assumed. -/
noncomputable section
open Set Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.KdV

def hillHminusLocalLogNorming (m : ℕ+) (a : PeriodOneHminusOne) (q : PeriodOneHminusOne) : ℂ :=
  (-2:ℂ)*normalizedLogChart (hillHminusDirichletNorming m) a 0 q

theorem hillHminusLocalLogNorming_base (m : ℕ+) (a : PeriodOneHminusOne)
    (ha : a ∈ hillHminusCanonicalDirichletDomain) : hillHminusLocalLogNorming m a a=0 := by
  rw [hillHminusLocalLogNorming,normalizedLogChart_base _ _ _ (hillHminusDirichletNorming_ne_zero m a ha),mul_zero]

theorem analyticAt_hillHminusLocalLogNorming (m : ℕ+) (a q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusCanonicalDirichletDomain)
    (hlog : hillHminusDirichletNorming m q/hillHminusDirichletNorming m a ∈ slitPlane) :
    AnalyticAt ℂ (hillHminusLocalLogNorming m a) q :=
  analyticAt_const.mul (normalizedLogChart_analyticAt _ a q 0
    (analyticOnNhd_hillHminusDirichletNorming m q hq) hlog)

theorem analyticAt_hillHminusLocalLogNorming_base (m : ℕ+) (a : PeriodOneHminusOne)
    (ha : a ∈ hillHminusCanonicalDirichletDomain) : AnalyticAt ℂ (hillHminusLocalLogNorming m a) a := by
  apply analyticAt_hillHminusLocalLogNorming m a a ha
  simp [hillHminusDirichletNorming_ne_zero m a ha]

theorem fderiv_hillHminusLocalLogNorming (m : ℕ+) (a q : PeriodOneHminusOne)
    (ha : a ∈ hillHminusCanonicalDirichletDomain) (hq : q ∈ hillHminusCanonicalDirichletDomain)
    (hlog : hillHminusDirichletNorming m q/hillHminusDirichletNorming m a ∈ slitPlane) :
    fderiv ℂ (hillHminusLocalLogNorming m a) q=
      ((-2:ℂ)*(hillHminusDirichletNorming m q)⁻¹) • fderiv ℂ (hillHminusDirichletNorming m) q := by
  have hd := (normalizedLogChart_hasFDerivAt (hillHminusDirichletNorming m) a q 0
    (hillHminusDirichletNorming_ne_zero m a ha)
    (analyticOnNhd_hillHminusDirichletNorming m q hq).differentiableAt hlog).const_smul (-2:ℂ)
  change HasFDerivAt (hillHminusLocalLogNorming m a)
    ((-2:ℂ) • ((hillHminusDirichletNorming m q)⁻¹ • fderiv ℂ (hillHminusDirichletNorming m) q)) q at hd
  simpa only [smul_smul] using hd.fderiv

theorem hillHminus_Dirichlet_localLogNorming_Gardner_matrix (n m : ℕ+) (a q : PeriodOneHminusOne)
    (ha : a ∈ hillHminusCanonicalDirichletDomain) (hq : q ∈ hillHminusCanonicalDirichletDomain)
    (hlog : hillHminusDirichletNorming m q/hillHminusDirichletNorming m a ∈ slitPlane) :
    NLS.Poisson.hminusGardnerBracket (hillHminusCanonicalDirichlet n) (hillHminusLocalLogNorming m a) q=
      (if n=m then 1 else 0) := by
  change NLS.Poisson.gardnerCotangentBivector (fderiv ℂ (hillHminusCanonicalDirichlet n) q)
    (fderiv ℂ (hillHminusLocalLogNorming m a) q)=_
  rw [fderiv_hillHminusLocalLogNorming m a q ha hq hlog,map_smul]
  change ((-2:ℂ)*(hillHminusDirichletNorming m q)⁻¹)*
    NLS.Poisson.hminusGardnerBracket (hillHminusCanonicalDirichlet n) (hillHminusDirichletNorming m) q=_
  rw [hillHminus_Dirichlet_norming_Gardner_matrix n m q hq]
  by_cases hnm : n=m
  · rw [if_pos hnm,if_pos hnm]
    have hn := hillHminusDirichletNorming_ne_zero m q hq
    field_simp
  · rw [if_neg hnm,if_neg hnm,mul_zero]

theorem hillHminus_Dirichlet_localLogNorming_Gardner_at_base (n m : ℕ+) (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusCanonicalDirichletDomain) :
    NLS.Poisson.hminusGardnerBracket (hillHminusCanonicalDirichlet n) (hillHminusLocalLogNorming m q) q=
      (if n=m then 1 else 0) := by
  apply hillHminus_Dirichlet_localLogNorming_Gardner_matrix n m q q hq hq
  simp [hillHminusDirichletNorming_ne_zero m q hq]

end NLS.KdV
