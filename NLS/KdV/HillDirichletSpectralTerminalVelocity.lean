import NLS.KdV.HillDirichletSpectralVectorField
import NLS.KdV.HillDirichletSheetLocalCancellation
import NLS.ComplexAnalysis.MovingSpectralParameter

/-! The actual terminal velocities of the native indexed fields.
The moving trace has both its source and energy derivatives. Analytic
sheet cancellation fills the resulting identity at branch endpoints. -/
noncomputable section
open Set Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.KdV

theorem analyticOnNhd_hillHminusDiscriminantEnergyDerivative_joint :
    AnalyticOnNhd ℂ (fun t : ℂ × PeriodOneHminusOne =>
      deriv (hillHminusDiscriminant t.2) t.1) univ := by
  let ev : ((ℂ × PeriodOneHminusOne) →L[ℂ] ℂ) →L[ℂ] ℂ :=
    ContinuousLinearMap.apply ℂ ℂ (1,0)
  have ha := ev.comp_analyticOnNhd analyticOnNhd_hillHminusDiscriminant_joint.fderiv
  convert ha using 1
  funext t
  exact deriv_spectral_section_eq_fderiv
    (fun s : ℂ × PeriodOneHminusOne => hillHminusDiscriminant s.2 s.1) t.1 t.2
      (analyticOnNhd_hillHminusDiscriminant_joint t (mem_univ _)).differentiableAt

theorem analyticOnNhd_hillHminusDiscriminantEnergyDerivative_at_Dirichlet (j : ℕ+) :
    AnalyticOnNhd ℂ (fun q => deriv (hillHminusDiscriminant q)
      (hillHminusCanonicalDirichlet j q)) hillHminusCanonicalDirichletDomain := by
  intro q hq
  exact (analyticOnNhd_hillHminusDiscriminantEnergyDerivative_joint
    (hillHminusCanonicalDirichlet j q,q) (mem_univ _)).comp
      (f := fun p : PeriodOneHminusOne => (hillHminusCanonicalDirichlet j p,p))
      ((analyticOnNhd_hillHminusCanonicalDirichlet j q hq).prod analyticAt_id)

theorem fderiv_hillHminusMovingDiscriminant_spectralVector (j k : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ hillHminusCanonicalDirichletDomain) :
    (fderiv ℂ (fun p => hillHminusDiscriminant p (hillHminusCanonicalDirichlet j p)) q)
      (hillHminusDirichletSpectralVector k q) =
      deriv (hillHminusDiscriminant q) (hillHminusCanonicalDirichlet j q)*
        (if j=k then hillHminusDirichletSheet j q/2 else 0) := by
  rw [fderiv_moving_spectral_parameter
    (fun t : ℂ × PeriodOneHminusOne => hillHminusDiscriminant t.2 t.1)
    (hillHminusCanonicalDirichlet j) q
    (analyticOnNhd_hillHminusDiscriminant_joint _ (mem_univ _)).differentiableAt
    (analyticOnNhd_hillHminusCanonicalDirichlet j q hq).differentiableAt]
  simp only [add_apply,smul_apply,smul_eq_mul]
  change hillHminusDiscriminantCotangent _ q (hillHminusDirichletSpectralVector k q)+_=_
  rw [hillHminusDirichletSpectralVector_isospectral,zero_add,
    fderiv_hillHminusDirichlet_spectralVector j k q hq]

theorem hillHminusDirichletNorming_spectralVector_cleared (j k : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ hillHminusCanonicalDirichletDomain) :
    hillHminusDirichletSheet j q *
      ((fderiv ℂ (hillHminusDirichletNorming j) q) (hillHminusDirichletSpectralVector k q)-
        (if j=k then -hillHminusDirichletNorming j q*
          deriv (hillHminusDiscriminant q) (hillHminusCanonicalDirichlet j q)/2 else 0))=0 := by
  have hn := hillHminusDirichletNorming_ne_zero j q hq
  have he : (fun p => hillHminusDiscriminant p (hillHminusCanonicalDirichlet j p)) =ᶠ[𝓝 q]
      (fun p => (hillHminusDirichletNorming j p)⁻¹+hillHminusDirichletNorming j p) := by
    filter_upwards [isOpen_hillHminusCanonicalDirichletDomain.mem_nhds hq] with p hp
    exact hillHminusDiscriminant_at_canonicalDirichlet j p hp
  have hd := ((hasDerivAt_inv hn).add (hasDerivAt_id (hillHminusDirichletNorming j q))).comp_hasFDerivAt q
    (analyticOnNhd_hillHminusDirichletNorming j q hq).differentiableAt.hasFDerivAt
  change HasFDerivAt (fun p => (hillHminusDirichletNorming j p)⁻¹+hillHminusDirichletNorming j p) _ q at hd
  have hv := fderiv_hillHminusMovingDiscriminant_spectralVector j k q hq
  rw [he.fderiv_eq,hd.fderiv] at hv
  simp only [smul_apply,smul_eq_mul] at hv
  dsimp only [hillHminusDirichletSheet] at hv ⊢
  split_ifs at hv ⊢ <;> field_simp [hn] at hv ⊢ <;> linear_combination -hv

theorem fderiv_hillHminusDirichletNorming_spectralVector (j k : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ hillHminusCanonicalDirichletDomain) :
    (fderiv ℂ (hillHminusDirichletNorming j) q) (hillHminusDirichletSpectralVector k q)=
      if j=k then -hillHminusDirichletNorming j q*
        deriv (hillHminusDiscriminant q) (hillHminusCanonicalDirichlet j q)/2 else 0 := by
  have hF : AnalyticOnNhd ℂ (fun p =>
      (fderiv ℂ (hillHminusDirichletNorming j) p) (hillHminusDirichletSpectralVector k p))
      hillHminusCanonicalDirichletDomain :=
    fun p hp => ((ContinuousLinearMap.id ℂ (PeriodOneHminusOne →L[ℂ] ℂ)).analyticAt_bilinear _).comp
      (((analyticOnNhd_hillHminusDirichletNorming j).fderiv p hp).prod
        (analyticOnNhd_hillHminusDirichletSpectralVector k p hp))
  have hG : AnalyticOnNhd ℂ (fun p => if j=k then -hillHminusDirichletNorming j p*
      deriv (hillHminusDiscriminant p) (hillHminusCanonicalDirichlet j p)/2 else 0)
      hillHminusCanonicalDirichletDomain := by
    split_ifs
    · exact ((analyticOnNhd_hillHminusDirichletNorming j).neg.mul
        (analyticOnNhd_hillHminusDiscriminantEnergyDerivative_at_Dirichlet j)).div_const
    · exact analyticOnNhd_const
  exact hillHminusDirichletSheet_cancel_analytic j hillHminusCanonicalDirichletDomain
    isOpen_hillHminusCanonicalDirichletDomain isConnected_hillHminusCanonicalDirichletDomain.isPreconnected
    isConnected_hillHminusCanonicalDirichletDomain.nonempty (subset_refl _) _ _ hF hG
    (fun p hp => hillHminusDirichletNorming_spectralVector_cleared j k p hp) hq

theorem fderiv_hillHminusDirichletSheet_spectralVector (j k : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ hillHminusCanonicalDirichletDomain) :
    (fderiv ℂ (hillHminusDirichletSheet j) q) (hillHminusDirichletSpectralVector k q)=
      if j=k then hillHminusDiscriminant q (hillHminusCanonicalDirichlet j q)*
        deriv (hillHminusDiscriminant q) (hillHminusCanonicalDirichlet j q)/2 else 0 := by
  have hn := hillHminusDirichletNorming_ne_zero j q hq
  have hd := ((hasDerivAt_inv hn).sub (hasDerivAt_id (hillHminusDirichletNorming j q))).comp_hasFDerivAt q
    (analyticOnNhd_hillHminusDirichletNorming j q hq).differentiableAt.hasFDerivAt
  change HasFDerivAt (hillHminusDirichletSheet j) _ q at hd
  rw [hd.fderiv]
  simp only [smul_apply,smul_eq_mul]
  rw [fderiv_hillHminusDirichletNorming_spectralVector j k q hq,
    hillHminusDiscriminant_at_canonicalDirichlet j q hq]
  split_ifs <;> field_simp [hn] <;> ring

end NLS.KdV
