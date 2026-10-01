import NLS.ZakharovShabat.SourceAngularEtaRemainderIsospectral
import NLS.ZakharovShabat.SourceAngularEtaDifferential

/-! # The actual diagonal eta differential in isospectral directions

Differentiating the actual half-gap and cosine-point equations gives
the model-angle variation with its terminal root factor retained.
Adding the actual remainder variation cancels the model numerator.
The single eta phase supplies the same cotangent for every local chart.
-/

noncomputable section
set_option maxHeartbeats 800000
open Set Metric Complex Filter Topology NLS.ComplexAnalysis NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceAngularEtaAnalyticChartData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {m : ℤ}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}
  {W V U : Set (CoeffPair p)} {c : ℤ → ℂ} {T : ℤ → ℝ}
  {r R : ℝ} {z₀ : ℂ} {ρ : ℝ} {δ ε : CoeffPair p → ℂ}

/-- The actual model angle variation holds at either periodic terminal.
Only the chart's open selected gap is needed; the terminal may be a branch. -/
theorem fderiv_modelAngle_isospectral_cleared
    (D : SourceAngularEtaAnalyticChartData hp hp1 m s W V U c T r R z₀ ρ δ ε)
    (φ : realTypeSourceLocus p) (hφ : φ.val ∈ U)
    (h : CoeffPair p) (hiso : SourceIsospectralDirection hp φ.val h) :
    let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val m
    sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet m φ.val *
        (fderiv ℂ ε φ.val) h =
      I*(2*I*sourceStandardRootOmittedProduct hp hp1 m φ.val μ) *
        (fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m) φ.val) h := by
  dsimp only
  let M : CoeffPair p → ℂ := fun ψ => sourceStandardRootMidpoint hp hp1 ψ m
  let G : CoeffPair p → ℂ := fun ψ => (canonicalPeriodicGap hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) m)^2
  let μ : CoeffPair p → ℂ := fun ψ => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m
  obtain ⟨A,_,_,hAreal,hMG⟩ := exists_global_source_analytic_midpoint_squaredGap hp hp1
  have hM : DifferentiableAt ℂ M φ.val := (hMG φ.val (hAreal φ.property) m).1.differentiableAt
  have hG : DifferentiableAt ℂ G φ.val := (hMG φ.val (hAreal φ.property) m).2.differentiableAt
  have hMGzero : (fderiv ℂ M φ.val) h = 0 ∧ (fderiv ℂ G φ.val) h = 0 :=
    fderiv_canonicalPeriodicMidpoint_squaredGap_isospectral_eq_zero hp hp1 φ.val φ.property h hiso m
  have hδ : DifferentiableAt ℂ δ φ.val := (D.angle.halfGap_analytic φ.val hφ).differentiableAt
  have hε : DifferentiableAt ℂ ε φ.val := (D.angle.angle_analytic φ.val hφ).differentiableAt
  have hδnear : (fun ψ : CoeffPair p => δ ψ^2) =ᶠ[𝓝 φ.val] (fun ψ => G ψ/4) := by
    filter_upwards [D.angle.source_open.mem_nhds hφ] with ψ hψ
    rw [D.angle.halfGap_sq ψ hψ]
    dsimp only [G]
    ring
  have hδzero : (fderiv ℂ δ φ.val) h = 0 := by
    have he := congrArg (fun L : CoeffPair p →L[ℂ] ℂ => L h) hδnear.fderiv_eq
    have hl := (hδ.hasFDerivAt.pow 2).fderiv
    have hr := (hG.hasFDerivAt.mul_const (4 : ℂ)⁻¹).fderiv
    change fderiv ℂ (fun ψ : CoeffPair p => δ ψ^2) φ.val = _ at hl
    change fderiv ℂ (fun ψ : CoeffPair p => G ψ/4) φ.val = _ at hr
    rw [hl,hr] at he
    simp only [smul_apply,smul_eq_mul,hMGzero.2,mul_zero] at he
    apply mul_left_cancel₀ (D.angle.halfGap_ne_zero φ.val hφ)
    rw [mul_zero]
    linear_combination he/2
  have hμnear : (fun ψ : CoeffPair p => M ψ+δ ψ*Complex.cos (ε ψ)) =ᶠ[𝓝 φ.val] μ := by
    filter_upwards [D.angle.source_open.mem_nhds hφ] with ψ hψ
    exact (D.angle.terminal_coordinates ψ hψ).1
  have hμvariation : (fderiv ℂ μ φ.val) h =
      -(δ φ.val*Complex.sin (ε φ.val))*(fderiv ℂ ε φ.val) h := by
    have he := congrArg (fun L : CoeffPair p →L[ℂ] ℂ => L h) hμnear.fderiv_eq
    have hd := (hM.hasFDerivAt.fun_add (hδ.hasFDerivAt.fun_mul hε.hasFDerivAt.ccos)).fderiv
    rw [hd] at he
    simp only [add_apply,smul_apply,smul_eq_mul,hMGzero.1,hδzero,zero_add,mul_zero,add_zero] at he
    linear_combination -he
  have hroot : 2*δ φ.val*sourceStandardRootOmittedProduct hp hp1 m φ.val (μ φ.val)*Complex.sin (ε φ.val) =
      sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet m φ.val := by
    simpa only [sourceAngularBranchCosineRoot,(D.angle.terminal_coordinates φ.val hφ).1,
      sourceBoundaryTerminalAntiDiscriminant] using D.angle.terminal_root φ.val hφ
  change sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet m φ.val*(fderiv ℂ ε φ.val) h =
    I*(2*I*sourceStandardRootOmittedProduct hp hp1 m φ.val (μ φ.val))*(fderiv ℂ μ φ.val) h
  calc
    _ = -2*sourceStandardRootOmittedProduct hp hp1 m φ.val (μ φ.val)*(fderiv ℂ μ φ.val) h := by
      rw [← hroot,hμvariation]
      ring
    _ = _ := by
      linear_combination -2*sourceStandardRootOmittedProduct hp hp1 m φ.val (μ φ.val)*
        (fderiv ℂ μ φ.val) h*Complex.I_sq

/-- The actual full eta representative has the normalized numerator
weight after its model and remainder terms cancel. Branch terminals are included. -/
theorem fderiv_etaRepresentative_isospectral_cleared
    (D : SourceAngularEtaAnalyticChartData hp hp1 m s W V U c T r R z₀ ρ δ ε)
    {W₀ : Set (CoeffPair p)} (hs : SourcePsiIsolatingComplexExtension hp hp1 W₀ s)
    (φ : realTypeSourceLocus p) (hφ : φ.val ∈ U) (hφ₀ : φ.val ∈ W₀)
    (h : CoeffPair p) (hiso : SourceIsospectralDirection hp φ.val h) :
    let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val m
    sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet m φ.val *
        (fderiv ℂ (sourceAngularEtaCauchyRepresentative hp hp1 m s (c m) r R z₀ ρ ε) φ.val) h =
      sourcePsiCandidate m (μ,(s m φ.val : Coeff p)) *
        (fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m) φ.val) h := by
  dsimp only
  have hε := (D.angle.angle_analytic φ.val hφ).differentiableAt
  have hμ := analyticAt_canonicalPeriodOneBoundaryRoots_of_realType hp hp1 .dirichlet φ.val φ.property m
  have hR := (D.annulus.analyticAt_etaRemainderCauchyCandidate ρ D.inner_lt_cauchy D.cauchy_lt_outer
    φ.val (D.angle.source_subset hφ) hμ).differentiableAt
  have hd := ((hε.hasFDerivAt.sub_const (Real.pi : ℂ)).fun_add hR.hasFDerivAt).fderiv
  change fderiv ℂ (sourceAngularEtaCauchyRepresentative hp hp1 m s (c m) r R z₀ ρ ε) φ.val = _ at hd
  rw [hd]
  simp only [add_apply]
  have hmodel := D.fderiv_modelAngle_isospectral_cleared φ hφ h hiso
  have hrem := D.annulus.fderiv_etaRemainder_isospectral_cleared hs ρ D.inner_lt_cauchy D.cauchy_lt_outer
    φ (D.angle.source_subset hφ) hφ₀ h hiso
  dsimp only at hmodel hrem
  linear_combination hmodel+hrem

/-- The single actual eta cotangent has the same cleared isospectral
variation as every local representative. -/
theorem etaDifferential_isospectral_cleared
    (D : SourceAngularEtaAnalyticChartData hp hp1 m s W V U c T r R z₀ ρ δ ε)
    {W₀ : Set (CoeffPair p)} (hs : SourcePsiIsolatingComplexExtension hp hp1 W₀ s)
    (φ : realTypeSourceLocus p) (hφ : φ.val ∈ U) (hφ₀ : φ.val ∈ W₀)
    (h : CoeffPair p) (hiso : SourceIsospectralDirection hp φ.val h) :
    let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val m
    sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet m φ.val *
        sourceAngularEtaDifferential hp hp1 m s φ.val h =
      sourcePsiCandidate m (μ,(s m φ.val : Coeff p)) *
        (fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m) φ.val) h := by
  rw [D.etaDifferential_eq_fderiv_representative φ.val hφ]
  exact D.fderiv_etaRepresentative_isospectral_cleared hs φ hφ hφ₀ h hiso

/-- Every actual action gives the normalized eta/root bracket equation
for the single eta cotangent, also at periodic Dirichlet terminals. -/
theorem sourceBivector_etaDifferential_action_cleared
    (D : SourceAngularEtaAnalyticChartData hp hp1 m s W V U c T r R z₀ ρ δ ε)
    {W₀ : Set (CoeffPair p)} (hs : SourcePsiIsolatingComplexExtension hp hp1 W₀ s)
    (h2p : (2 : ℝ≥0∞) ≤ p) (k : ℤ)
    (φ : realTypeSourceLocus p) (hφ : φ.val ∈ U) (hφ₀ : φ.val ∈ W₀) :
    let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val m
    sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet m φ.val *
        sourceBivector h2p (sourceAngularEtaDifferential hp hp1 m s φ.val)
          (fderiv ℂ (sourceComplexAction hp hp1 k) φ.val) =
      sourcePsiCandidate m (μ,(s m φ.val : Coeff p)) *
        sourceBracket h2p (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m)
          (sourceComplexAction hp hp1 k) φ.val := by
  have ht := D.etaDifferential_isospectral_cleared hs φ hφ hφ₀
    (sourceHamiltonianVector h2p (sourceComplexAction hp hp1 k) φ.val)
    (sourceHamiltonianVector_action_isospectral hp hp1 h2p φ.val φ.property k)
  simpa only [sourceHamiltonianVector,apply_sourceHamiltonianDirection,sourceBracket] using ht

/-- At a regular terminal the actual eta/action bracket has the same
normalized differential weight as the off-diagonal beta/root brackets. -/
theorem sourceBivector_etaDifferential_action_eq_root_weight
    (D : SourceAngularEtaAnalyticChartData hp hp1 m s W V U c T r R z₀ ρ δ ε)
    {W₀ : Set (CoeffPair p)} (hs : SourcePsiIsolatingComplexExtension hp hp1 W₀ s)
    (h2p : (2 : ℝ≥0∞) ≤ p) (k : ℤ)
    (φ : realTypeSourceLocus p) (hφ : φ.val ∈ U) (hφ₀ : φ.val ∈ W₀)
    (hδ : sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet m φ.val ≠ 0) :
    let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val m
    sourceBivector h2p (sourceAngularEtaDifferential hp hp1 m s φ.val)
      (fderiv ℂ (sourceComplexAction hp hp1 k) φ.val) =
      sourcePsiCandidate m (μ,(s m φ.val : Coeff p)) /
        sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet m φ.val *
          sourceBracket h2p (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m)
            (sourceComplexAction hp hp1 k) φ.val := by
  dsimp only
  apply mul_left_cancel₀ hδ
  rw [D.sourceBivector_etaDifferential_action_cleared hs h2p k φ hφ hφ₀]
  field_simp [hδ]

/-- The actual angle/action bracket reduces to its proved diagonal
eta contribution and the derivative of the actual full beta correction. -/
theorem sourceBivector_thetaDifferential_action_diagonal_add_betaCorrection
    (D : SourceAngularEtaAnalyticChartData hp hp1 m s W V U c T r R z₀ ρ δ ε)
    {W₀ : Set (CoeffPair p)} (hs : SourcePsiIsolatingComplexExtension hp hp1 W₀ s)
    (hbeta : AnalyticOnNhd ℂ (sourceAngularBetaCorrection hp hp1 m s) U)
    (h2p : (2 : ℝ≥0∞) ≤ p) (k : ℤ)
    (φ : realTypeSourceLocus p) (hφ : φ.val ∈ U) (hφ₀ : φ.val ∈ W₀) :
    let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val m
    sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet m φ.val *
        sourceBivector h2p (sourceAngularThetaDifferential hp hp1 m s φ.val)
          (fderiv ℂ (sourceComplexAction hp hp1 k) φ.val) =
      sourcePsiCandidate m (μ,(s m φ.val : Coeff p)) *
        sourceBracket h2p (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m)
          (sourceComplexAction hp hp1 k) φ.val+
      sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet m φ.val *
        sourceBracket h2p (sourceAngularBetaCorrection hp hp1 m s) (sourceComplexAction hp hp1 k) φ.val := by
  rw [D.thetaDifferential_eq_eta_add_betaCorrection hbeta φ.val hφ]
  simp only [map_add,add_apply]
  have ht := D.sourceBivector_etaDifferential_action_cleared hs h2p k φ hφ hφ₀
  dsimp only at ht ⊢
  change _ = _+sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet m φ.val *
    sourceBivector h2p (fderiv ℂ (sourceAngularBetaCorrection hp hp1 m s) φ.val)
      (fderiv ℂ (sourceComplexAction hp hp1 k) φ.val)
  linear_combination ht

end SourceAngularEtaAnalyticChartData
end NLS.ZakharovShabat
