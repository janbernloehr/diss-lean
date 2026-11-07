import NLS.KdV.HminusOneCanonicalHillPsiRealZero
import NLS.ComplexAnalysis.AnalyticImplicitScalarExistence

/-! Every original retained zero at a REAL native source extends to
a genuine locally analytic simple zero branch on a complex native
neighborhood. Neighborhoods here may depend on both zero indices;
no common all-index extension or fine zero estimate is claimed. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.KdV

theorem exists_local_analytic_hillHminusPsi_simple_zero
    (n : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ hillHminusCanonicalPsiDomain) (a : ℂ)
    (ha : hillHminusCanonicalPsi n (a,q) = 0)
    (hd : deriv (fun E : ℂ => hillHminusCanonicalPsi n (E,q)) a ≠ 0) :
    ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ q ∈ U ∧ U ⊆ hillHminusCanonicalPsiDomain ∧
      ∃ s : PeriodOneHminusOne → ℂ, AnalyticOnNhd ℂ s U ∧ s q = a ∧
        ∀ y ∈ U, hillHminusCanonicalPsi n (s y,y) = 0 ∧
          deriv (fun E : ℂ => hillHminusCanonicalPsi n (E,y)) (s y) ≠ 0 := by
  have hF := analyticOnNhd_hillHminusCanonicalPsi n (a,q) ⟨mem_univ _,hq⟩
  have hpartial : (fderiv ℂ (hillHminusCanonicalPsi n) (a,q)) (1,0) ≠ 0 := by
    rw [← deriv_spectral_section_eq_fderiv (hillHminusCanonicalPsi n) a q hF.differentiableAt]
    exact hd
  obtain ⟨s,hsa,hsq,hroot⟩ := exists_analytic_implicitScalarRoot (hillHminusCanonicalPsi n) a q hF ha hpartial
  have hD : IsOpen (univ ×ˢ hillHminusCanonicalPsiDomain : Set (ℂ × PeriodOneHminusOne)) :=
    isOpen_univ.prod isOpen_hillHminusCanonicalPsiDomain
  have hderiv : ContinuousAt (fun y : PeriodOneHminusOne =>
      deriv (fun E : ℂ => hillHminusCanonicalPsi n (E,y)) (s y)) q :=
    ((continuousOn_spectral_deriv_of_analyticOnNhd (hillHminusCanonicalPsi n) _ hD
      (analyticOnNhd_hillHminusCanonicalPsi n)).continuousAt
      (hD.mem_nhds ⟨mem_univ _,hq⟩)).comp (hsa.continuousAt.prodMk continuousAt_id)
  have hderivq : deriv (fun E : ℂ => hillHminusCanonicalPsi n (E,q)) (s q) ≠ 0 := by rw [hsq]; exact hd
  have hnear := ((hsa.eventually_analyticAt.and hroot).and
    (isOpen_hillHminusCanonicalPsiDomain.mem_nhds hq)).and (hderiv.eventually_ne hderivq)
  obtain ⟨r,hrpos,hball⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨ball q r,isOpen_ball,mem_ball_self hrpos,(fun y hy => (hball hy).1.2),s,?_,hsq,?_⟩
  · exact fun y hy => (hball hy).1.1.1
  · exact fun y hy => ⟨(hball hy).1.1.2,(hball hy).2⟩

theorem exists_local_analytic_hillHminusCanonicalPsi_retained_zero
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (n m : ℕ+) (hmn : m ≠ n) :
    ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ q ∈ U ∧ U ⊆ hillHminusCanonicalPsiDomain ∧
      ∃ s : PeriodOneHminusOne → ℂ, AnalyticOnNhd ℂ s U ∧
        s q = (hillHminusCanonicalPsiRealZero n m q hr:ℂ) ∧
        ∀ y ∈ U, hillHminusCanonicalPsi n (s y,y) = 0 ∧
          deriv (fun E : ℂ => hillHminusCanonicalPsi n (E,y)) (s y) ≠ 0 := by
  have hzero := hillHminusCanonicalPsiRealZero_is_zero n m q hr hmn
  exact exists_local_analytic_hillHminusPsi_simple_zero n q
    (real_mem_hillHminusCanonicalPsiDomain q hr) _ hzero
    (hillHminusCanonicalPsi_deriv_ne_zero_of_real_source q hr n _ hzero)

end NLS.KdV
