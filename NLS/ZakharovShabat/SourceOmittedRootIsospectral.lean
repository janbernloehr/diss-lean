import NLS.ZakharovShabat.SourceStandardRootIsospectral

/-! # Stationarity of the actual infinite omitted-root products

Every retained factor is stationary in an isospectral direction.
The actual literal finite products are therefore stationary. Their
locally uniform analytic approximation gives convergence of the full
Fréchet derivatives and proves the same result for the infinite product,
including on the selected gap and at either periodic endpoint.
-/

noncomputable section
set_option maxHeartbeats 800000
open Set Metric Complex Filter Topology NLS.ComplexAnalysis NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A literal finite omitted-root product is stationary in every
isospectral direction wherever its retained roots avoid their cuts. -/
theorem fderiv_sourceStandardRootOmittedPartialProduct_isospectral_eq_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p φ)) (h : CoeffPair p)
    (hiso : SourceIsospectralDirection hp φ h) (n : ℤ) (N : ℕ) (z : ℂ)
    (hz : z ∈ sourceStandardRootOmittedDomain hp hp1 φ n) :
    (fderiv ℂ (fun ψ : CoeffPair p =>
      sourceStandardRootOmittedPartialProduct hp hp1 n N (z,ψ)) φ) h = 0 := by
  classical
  let S := (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase n
  let F (m : ℤ) : CoeffPair p → ℂ :=
    fun ψ => sourceStandardRoot hp hp1 ψ m z / singleSpectralDenominator m
  obtain ⟨W,_,_,hWreal,hMG⟩ := exists_global_source_analytic_midpoint_squaredGap hp hp1
  have hd (m : ℤ) (hm : m ∈ S) : DifferentiableAt ℂ
      (fun ψ : CoeffPair p => sourceStandardRoot hp hp1 ψ m z) φ :=
    ((sourceStandardRoot_joint_analyticAt_of_symmetric hp hp1 φ m z
      (hMG φ (hWreal hreal) m).1 (hMG φ (hWreal hreal) m).2
      (hz m (Finset.mem_erase.mp hm).1)).comp
      (f := fun ψ : CoeffPair p => (z,ψ)) (analyticAt_const.prod analyticAt_id)).differentiableAt
  have hF (m : ℤ) (hm : m ∈ S) : HasFDerivAt (F m)
      ((singleSpectralDenominator m)⁻¹ • fderiv ℂ
        (fun ψ : CoeffPair p => sourceStandardRoot hp hp1 ψ m z) φ) φ := by
    simpa only [F,div_eq_mul_inv] using (hd m hm).hasFDerivAt.mul_const
      (singleSpectralDenominator m)⁻¹
  have hfinite := (HasFDerivAt.finsetProd hF).mul_const (singleSpectralDenominator n)⁻¹
  have he := congrArg (fun L : CoeffPair p →L[ℂ] ℂ => L h) hfinite.fderiv
  change (fderiv ℂ (fun ψ : CoeffPair p =>
      sourceStandardRootOmittedPartialProduct hp hp1 n N (z,ψ)) φ) h = _ at he
  rw [he]
  simp only [smul_apply,smul_eq_mul,sum_apply]
  have hsum : (∑ m ∈ S, (∏ j ∈ S.erase m, F j φ)*
      ((singleSpectralDenominator m)⁻¹*
        (fderiv ℂ (fun ψ : CoeffPair p => sourceStandardRoot hp hp1 ψ m z) φ) h)) = 0 := by
    apply Finset.sum_eq_zero
    intro m hm
    rw [fderiv_sourceStandardRoot_isospectral_eq_zero hp hp1 φ hreal h hiso m z
      (hz m (Finset.mem_erase.mp hm).1),mul_zero,mul_zero]
  rw [hsum,mul_zero]

/-- The actual infinite omitted-root product is stationary throughout
its full domain, including points of the selected gap and its endpoints.
The derivative limit is justified by actual local uniform analyticity. -/
theorem fderiv_sourceStandardRootOmittedProduct_isospectral_eq_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p φ)) (h : CoeffPair p)
    (hiso : SourceIsospectralDirection hp φ h) (n : ℤ) (z : ℂ)
    (hz : z ∈ sourceStandardRootOmittedDomain hp hp1 φ n) :
    (fderiv ℂ (fun ψ : CoeffPair p => sourceStandardRootOmittedProduct hp hp1 n ψ z) φ) h = 0 := by
  obtain ⟨W,_,_,hWreal,hfinite⟩ := exists_global_source_open_analytic_omittedPartialProduct hp hp1
  let D := sourceStandardRootOmittedJointDomain hp hp1 W n
  let P := sourceStandardRootOmittedJointProduct hp hp1 n
  have hpoint : (z,φ) ∈ D := ⟨hWreal hreal,hz⟩
  have huniform (t : ℂ × CoeffPair p) (ht : t ∈ D) :
      ∃ U : Set (ℂ × CoeffPair p), IsOpen U ∧ t ∈ U ∧
        TendstoUniformlyOn (sourceStandardRootOmittedPartialProduct hp hp1 n) P atTop U :=
    exists_local_uniform_sourceStandardRootOmittedProduct hp hp1 n t.2 t.1
      (fun N => ((hfinite n).2 N t ht).continuousAt)
  have happ := HasLocalUniformAnalyticApproximationOn.of_open_local_uniform
    (hfinite n).1 (hfinite n).2 huniform
  obtain ⟨r,hr,_,hconv⟩ := happ.uniform_fderiv (z,φ) hpoint
  have hlim := hconv.tendsto_at (mem_ball_self hr)
  have hcont : Continuous (fun L : (ℂ × CoeffPair p) →L[ℂ] ℂ => L (0,h)) := by fun_prop
  have heval := hcont.continuousAt.tendsto.comp hlim
  have hfinitezero (N : ℕ) :
      (fderiv ℂ (sourceStandardRootOmittedPartialProduct hp hp1 n N) (z,φ)) (0,h) = 0 := by
    have hsection := fderiv_source_section_eq_joint
      (sourceStandardRootOmittedPartialProduct hp hp1 n N) z φ
      ((hfinite n).2 N (z,φ) hpoint).differentiableAt
    have he := congrArg (fun L : CoeffPair p →L[ℂ] ℂ => L h) hsection
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.inr_apply] at he
    rw [← he]
    exact fderiv_sourceStandardRootOmittedPartialProduct_isospectral_eq_zero hp hp1 φ hreal h hiso n N z hz
  simp only [Function.comp_def,hfinitezero] at heval
  have hzero : (fderiv ℂ P (z,φ)) (0,h) = 0 := tendsto_nhds_unique heval tendsto_const_nhds
  have hPdiff : DifferentiableAt ℂ P (z,φ) :=
    (happ.differentiableOn (z,φ) hpoint).differentiableAt ((hfinite n).1.mem_nhds hpoint)
  change (fderiv ℂ (fun ψ : CoeffPair p => P (z,ψ)) φ) h = 0
  rw [fderiv_source_section_eq_joint P z φ hPdiff]
  simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.inr_apply] using hzero

/-- Every actual action fixes every actual omitted-root product on
its full domain, with no exclusion of the selected gap. -/
theorem sourceBracket_omittedRootProduct_action_eq_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ))
    (n m : ℤ) (z : ℂ) (hz : z ∈ sourceStandardRootOmittedDomain hp hp1 φ n) :
    sourceBracket h2p (fun ψ : CoeffPair p => sourceStandardRootOmittedProduct hp hp1 n ψ z)
      (sourceComplexAction hp hp1 m) φ = 0 := by
  rw [← fderiv_apply_sourceHamiltonianVector]
  exact fderiv_sourceStandardRootOmittedProduct_isospectral_eq_zero hp hp1 φ hreal _
    (sourceHamiltonianVector_action_isospectral hp hp1 h2p φ hreal m) n z hz

end NLS.ZakharovShabat
