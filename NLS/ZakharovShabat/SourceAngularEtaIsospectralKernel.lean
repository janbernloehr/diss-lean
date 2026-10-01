import NLS.ZakharovShabat.SourceAngularTerminalIsospectralFlow
import NLS.ZakharovShabat.SourceAngularEtaIsospectral

/-! # The actual diagonal eta kernel in general isospectral sheet flows

Both differentiated terminal equations determine the model-angle velocity
at periodic endpoints. Its model term cancels the actual Cauchy remainder,
leaving the single eta cotangent with the normalized terminal kernel.
-/

noncomputable section
set_option maxHeartbeats 800000
open Set Metric Complex Filter Topology NLS.ComplexAnalysis NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceAngularJointAnnulusChartData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {m : ℤ}
  {s : (j : ℤ) → CoeffPair p → DeletedCoeff p j}
  {W V : Set (CoeffPair p)} {c : ℤ → ℂ} {T : ℤ → ℝ} {r R : ℝ} {z₀ : ℂ}

/-- The actual remainder retains the model term in a general
isospectral sheet flow, including a collapsed selected gap. -/
theorem fderiv_etaRemainder_isospectral_eq_kernel
    (D : SourceAngularJointAnnulusChartData hp hp1 m s W V c T r R z₀)
    {W₀ : Set (CoeffPair p)} (hs : SourcePsiIsolatingComplexExtension hp hp1 W₀ s)
    (ρ : ℝ) (hrρ : r < ρ) (hρR : ρ < R) (φ : realTypeSourceLocus p)
    (hφ : φ.val ∈ V) (hφ₀ : φ.val ∈ W₀)
    (h : CoeffPair p) (hiso : SourceIsospectralDirection hp φ.val h) (v : ℂ)
    (hroot₀ : (fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m) φ.val) h =
      sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet m φ.val*v)
    (hanti₀ : (fderiv ℂ (sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet m) φ.val) h =
      let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val m
      canonicalDiscriminant hp (periodOnePotential φ.val) μ*
        deriv (canonicalDiscriminant hp (periodOnePotential φ.val)) μ*v) :
    let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val m
    (fderiv ℂ (sourceAngularEtaRemainderCauchyCandidate hp hp1 m s (c m) r R z₀ ρ) φ.val) h =
      (sourcePsiCandidate m (μ,(s m φ.val : Coeff p))-
        I*(2*I*sourceStandardRootOmittedProduct hp hp1 m φ.val μ))*
        v := by
  dsimp only
  let μ : CoeffPair p → ℂ := fun ψ => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m
  let S := sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet m
  let P : ℂ × CoeffPair p → ℂ := fun t => 2*I*sourceStandardRootOmittedJointProduct hp hp1 m t
  let K : CoeffPair p → ℂ := fun ψ => P (μ ψ,ψ)
  let K' := deriv (fun z => P (z,φ.val)) (μ φ.val)
  let M := sourceStandardRootMidpoint hp hp1 φ.val m
  let G := (canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) m)^2
  let Q := (μ φ.val-M)^2-G/4
  let H := sourceAngularEtaQuotientCauchyCandidate hp hp1 m s (c m) r R z₀ ρ
  have hterminal : μ φ.val ∈ ball (c m) ρ :=
    ball_subset_ball hrρ.le (D.terminal_enclosed φ.val hφ)
  have hflow := D.terminal_isospectral_flow φ hφ h hiso v hroot₀ hanti₀
  change K φ.val ≠ 0 ∧ (fderiv ℂ μ φ.val) h = S φ.val*v ∧
      (fderiv ℂ S φ.val) h = (K φ.val*K'*Q+K φ.val^2*(μ φ.val-M))*v ∧
      (fderiv ℂ K φ.val) h = K'*S φ.val*v ∧ S φ.val^2 = K φ.val^2*Q at hflow
  obtain ⟨hKne,hroot,hanti,hKflow,hsq⟩ := hflow
  have hrem := D.fderiv_etaRemainder_isospectral_terminal_eq hs ρ hrρ hρR φ hφ hφ₀ h hiso
  change K φ.val^2*(fderiv ℂ (sourceAngularEtaRemainderCauchyCandidate hp hp1 m s (c m) r R z₀ ρ) φ.val) h =
    ((fderiv ℂ S φ.val) h*K φ.val-S φ.val*(fderiv ℂ K φ.val) h)*H (μ φ.val,φ.val)+
      S φ.val*K φ.val*deriv (fun z => H (z,φ.val)) (μ φ.val)*(fderiv ℂ μ φ.val) h at hrem
  rw [hroot] at hrem
  have heq := D.etaQuotientCauchyCandidate_equation φ.val hφ ρ hrρ hρR (μ φ.val) hterminal
  have hresult := quadratic_sheet_terminal_variation_of_flow (S φ.val) (K φ.val) Q
    (μ φ.val-M) (H (μ φ.val,φ.val)) (deriv (fun z => H (z,φ.val)) (μ φ.val))
    (sourceAngularGapNumerator hp hp1 m m s φ.val (μ φ.val)-I) v K'
    ((fderiv ℂ S φ.val) h) ((fderiv ℂ K φ.val) h)
    ((fderiv ℂ (sourceAngularEtaRemainderCauchyCandidate hp hp1 m s (c m) r R z₀ ρ) φ.val) h)
    hKne hsq hanti hKflow heq hrem
  change (fderiv ℂ (sourceAngularEtaRemainderCauchyCandidate hp hp1 m s (c m) r R z₀ ρ) φ.val) h = _
  rw [hresult]
  change K φ.val*(sourcePsiCandidate m (μ φ.val,(s m φ.val : Coeff p))/K φ.val-I)*v = _
  field_simp [hKne]
  dsimp only [K,P,sourceStandardRootOmittedJointProduct,μ]
  ring

end SourceAngularJointAnnulusChartData
namespace SourceAngularEtaAnalyticChartData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {m : ℤ}
  {s : (j : ℤ) → CoeffPair p → DeletedCoeff p j}
  {W V U : Set (CoeffPair p)} {c : ℤ → ℂ} {T : ℤ → ℝ}
  {r R ρ : ℝ} {z₀ : ℂ} {δ ε : CoeffPair p → ℂ}

/-- The actual model angle's isospectral kernel includes either
periodic terminal, without dividing by the terminal sine. -/
theorem fderiv_modelAngle_isospectral_eq_kernel
    (D : SourceAngularEtaAnalyticChartData hp hp1 m s W V U c T r R z₀ ρ δ ε)
    (φ : realTypeSourceLocus p) (hφ : φ.val ∈ U)
    (h : CoeffPair p) (hiso : SourceIsospectralDirection hp φ.val h) (v : ℂ)
    (hroot₀ : (fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m) φ.val) h =
      sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet m φ.val*v)
    (hanti₀ : (fderiv ℂ (sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet m) φ.val) h =
      let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val m
      canonicalDiscriminant hp (periodOnePotential φ.val) μ*
        deriv (canonicalDiscriminant hp (periodOnePotential φ.val)) μ*v) :
    let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val m
    (fderiv ℂ ε φ.val) h =
      I*(2*I*sourceStandardRootOmittedProduct hp hp1 m φ.val μ)*v := by
  dsimp only
  let μ : CoeffPair p → ℂ := fun ψ => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m
  let S := sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet m
  let P : ℂ × CoeffPair p → ℂ := fun t => 2*I*sourceStandardRootOmittedJointProduct hp hp1 m t
  let K : CoeffPair p → ℂ := fun ψ => P (μ ψ,ψ)
  let K' := deriv (fun z => P (z,φ.val)) (μ φ.val)
  let M : CoeffPair p → ℂ := fun ψ => sourceStandardRootMidpoint hp hp1 ψ m
  let G := (canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) m)^2
  let Q := (μ φ.val-M φ.val)^2-G/4
  have hφV := D.angle.source_subset hφ
  have hflow := D.annulus.terminal_isospectral_flow φ hφV h hiso v hroot₀ hanti₀
  change K φ.val ≠ 0 ∧ (fderiv ℂ μ φ.val) h = S φ.val*v ∧
      (fderiv ℂ S φ.val) h = (K φ.val*K'*Q+K φ.val^2*(μ φ.val-M φ.val))*v ∧
      (fderiv ℂ K φ.val) h = K'*S φ.val*v ∧ S φ.val^2 = K φ.val^2*Q at hflow
  obtain ⟨hKne,hroot,hanti,hKflow,_⟩ := hflow
  obtain ⟨A,_,_,hAreal,hMG⟩ := exists_global_source_analytic_midpoint_squaredGap hp hp1
  have hM : DifferentiableAt ℂ M φ.val := (hMG φ.val (hAreal φ.property) m).1.differentiableAt
  have hMzero : (fderiv ℂ M φ.val) h = 0 :=
    (fderiv_canonicalPeriodicMidpoint_squaredGap_isospectral_eq_zero hp hp1 φ.val φ.property h hiso m).1
  have hδ : DifferentiableAt ℂ δ φ.val := (D.angle.halfGap_analytic φ.val hφ).differentiableAt
  have hδzero := D.fderiv_halfGap_isospectral_eq_zero φ hφ h hiso
  have hε : DifferentiableAt ℂ ε φ.val := (D.angle.angle_analytic φ.val hφ).differentiableAt
  have hgraph : AnalyticAt ℂ (fun ψ : CoeffPair p => (μ ψ,ψ)) φ.val :=
    (analyticAt_canonicalPeriodOneBoundaryRoots_of_realType hp hp1 .dirichlet φ.val φ.property m).prod analyticAt_id
  have hK : DifferentiableAt ℂ K φ.val :=
    ((analyticAt_const.mul (D.annulus.omitted_analytic (μ φ.val,φ.val)
      ⟨(D.annulus.disc_family φ.val hφV).dirichlet_mem_ball m,hφV⟩)).comp
      (f := fun ψ : CoeffPair p => (μ ψ,ψ)) hgraph).differentiableAt
  have hμnear : (fun ψ : CoeffPair p => M ψ+δ ψ*Complex.cos (ε ψ)) =ᶠ[𝓝 φ.val] μ := by
    filter_upwards [D.angle.source_open.mem_nhds hφ] with ψ hψ
    exact (D.angle.terminal_coordinates ψ hψ).1
  have hμvariation : (fderiv ℂ μ φ.val) h =
      -(δ φ.val*Complex.sin (ε φ.val))*(fderiv ℂ ε φ.val) h := by
    have he := congrArg (fun L : CoeffPair p →L[ℂ] ℂ => L h) hμnear.fderiv_eq
    have hd := (hM.hasFDerivAt.fun_add (hδ.hasFDerivAt.fun_mul hε.hasFDerivAt.ccos)).fderiv
    rw [hd] at he
    simp only [add_apply,smul_apply,smul_eq_mul,hMzero,hδzero,zero_add,mul_zero,add_zero] at he
    linear_combination -he
  have hSnear : (fun ψ : CoeffPair p => -I*δ ψ*K ψ*Complex.sin (ε ψ)) =ᶠ[𝓝 φ.val] S := by
    filter_upwards [D.angle.source_open.mem_nhds hφ] with ψ hψ
    have ht := D.angle.terminal_root ψ hψ
    simp only [sourceAngularBranchCosineRoot,(D.angle.terminal_coordinates ψ hψ).1] at ht
    change 2*δ ψ*sourceStandardRootOmittedProduct hp hp1 m ψ (μ ψ)*Complex.sin (ε ψ) = S ψ at ht
    dsimp only [K,P,sourceStandardRootOmittedJointProduct]
    linear_combination ht-2*δ ψ*sourceStandardRootOmittedProduct hp hp1 m ψ (μ ψ)*Complex.sin (ε ψ)*Complex.I_sq
  have hSnorm : S φ.val = -I*δ φ.val*K φ.val*Complex.sin (ε φ.val) := hSnear.eq_of_nhds.symm
  have hSvariation : (fderiv ℂ S φ.val) h = -I*δ φ.val*
      ((fderiv ℂ K φ.val) h*Complex.sin (ε φ.val)+K φ.val*Complex.cos (ε φ.val)*(fderiv ℂ ε φ.val) h) := by
    have he := congrArg (fun L : CoeffPair p →L[ℂ] ℂ => L h) hSnear.fderiv_eq
    have hd := ((((hasFDerivAt_const (-I) φ.val).fun_mul hδ.hasFDerivAt).fun_mul hK.hasFDerivAt).fun_mul hε.hasFDerivAt.csin).fderiv
    rw [hd] at he
    simp only [add_apply,smul_apply,smul_eq_mul,zero_apply,hδzero,mul_zero,add_zero] at he
    linear_combination -he
  have hcoords : M φ.val+δ φ.val*Complex.cos (ε φ.val) = μ φ.val :=
    (D.angle.terminal_coordinates φ.val hφ).1
  have hgap : δ φ.val^2 = G/4 := by
    rw [D.angle.halfGap_sq φ.val hφ]
    dsimp only [G]
    ring
  have hQ : Q = -δ φ.val^2*Complex.sin (ε φ.val)^2 := by
    dsimp only [Q]
    rw [← hcoords,add_sub_cancel_left,← hgap]
    linear_combination δ φ.val^2*Complex.sin_sq_add_cos_sq (ε φ.val)
  have hA : μ φ.val-M φ.val = δ φ.val*Complex.cos (ε φ.val) := by rw [← hcoords]; ring
  rw [hQ,hA] at hanti
  have hu : -δ φ.val*Complex.sin (ε φ.val)*(fderiv ℂ ε φ.val) h = S φ.val*v := by
    rw [← hroot,hμvariation]
    ring
  exact quadratic_cosine_angle_variation_of_flow (δ φ.val) (K φ.val) K'
    (Complex.sin (ε φ.val)) (Complex.cos (ε φ.val)) ((fderiv ℂ ε φ.val) h) v
    (S φ.val) ((fderiv ℂ S φ.val) h) ((fderiv ℂ K φ.val) h)
    (D.angle.halfGap_ne_zero φ.val hφ) hKne (Complex.sin_sq_add_cos_sq (ε φ.val)) hSnorm hu
    (by simpa only [mul_assoc] using hanti) hKflow hSvariation

/-- The actual single eta cotangent has the normalized sheet-flow
kernel on each open selected gap, for every finite `p > 1`. -/
theorem etaDifferential_isospectral_eq_kernel
    (D : SourceAngularEtaAnalyticChartData hp hp1 m s W V U c T r R z₀ ρ δ ε)
    {W₀ : Set (CoeffPair p)} (hs : SourcePsiIsolatingComplexExtension hp hp1 W₀ s)
    (φ : realTypeSourceLocus p) (hφ : φ.val ∈ U) (hφ₀ : φ.val ∈ W₀)
    (h : CoeffPair p) (hiso : SourceIsospectralDirection hp φ.val h) (v : ℂ)
    (hroot₀ : (fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m) φ.val) h =
      sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet m φ.val*v)
    (hanti₀ : (fderiv ℂ (sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet m) φ.val) h =
      let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val m
      canonicalDiscriminant hp (periodOnePotential φ.val) μ*
        deriv (canonicalDiscriminant hp (periodOnePotential φ.val)) μ*v) :
    let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val m
    (sourceAngularEtaDifferential hp hp1 m s φ.val) h =
      sourcePsiCandidate m (μ,(s m φ.val : Coeff p))*v := by
  dsimp only
  rw [D.etaDifferential_eq_fderiv_representative φ.val hφ]
  have hε := (D.angle.angle_analytic φ.val hφ).differentiableAt
  have hμ := analyticAt_canonicalPeriodOneBoundaryRoots_of_realType hp hp1 .dirichlet φ.val φ.property m
  have hR := (D.annulus.analyticAt_etaRemainderCauchyCandidate ρ D.inner_lt_cauchy D.cauchy_lt_outer
    φ.val (D.angle.source_subset hφ) hμ).differentiableAt
  have hd := ((hε.hasFDerivAt.sub_const (Real.pi : ℂ)).fun_add hR.hasFDerivAt).fderiv
  change fderiv ℂ (sourceAngularEtaCauchyRepresentative hp hp1 m s (c m) r R z₀ ρ ε) φ.val = _ at hd
  rw [hd]
  simp only [add_apply]
  have hmodel := D.fderiv_modelAngle_isospectral_eq_kernel φ hφ h hiso v hroot₀ hanti₀
  have hrem := D.annulus.fderiv_etaRemainder_isospectral_eq_kernel hs ρ D.inner_lt_cauchy D.cauchy_lt_outer
    φ (D.angle.source_subset hφ) hφ₀ h hiso v hroot₀ hanti₀
  dsimp only at hmodel hrem
  change (fderiv ℂ ε φ.val) h+
    (fderiv ℂ (sourceAngularEtaRemainderCauchyCandidate hp hp1 m s (c m) r R z₀ ρ) φ.val) h = _
  linear_combination hmodel+hrem

end SourceAngularEtaAnalyticChartData
end NLS.ZakharovShabat
