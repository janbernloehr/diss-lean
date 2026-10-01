import NLS.ZakharovShabat.SourceAngularBetaActionKernel
import NLS.ZakharovShabat.SourceAngularEtaIsospectral

/-! # The actual diagonal eta/action kernel through periodic terminals

The full moving sheet flow determines both the eta remainder and its
model angle without dividing by the terminal square root or its sine.
Their model terms cancel, giving the single eta cotangent the same
normalized action kernel as every off-diagonal beta contribution.
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

/-- The actual remainder/action kernel includes collapsed selected gaps
and retains the precise model numerator to be canceled by the angle. -/
theorem sourceBracket_etaRemainder_action_eq_kernel
    (D : SourceAngularJointAnnulusChartData hp hp1 m s W V c T r R z₀)
    {W₀ : Set (CoeffPair p)} (hs : SourcePsiIsolatingComplexExtension hp hp1 W₀ s)
    (h2p : (2 : ℝ≥0∞) ≤ p) (k : ℤ) (ρ : ℝ) (hrρ : r < ρ) (hρR : ρ < R)
    (ch : SourceRealActionBallChart hp hp1 k) (φ : realTypeSourceLocus p)
    (hφ : φ.val ∈ V) (hφ₀ : φ.val ∈ W₀) (hφch : φ.val ∈ ball ch.center ch.radius) :
    let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val m
    sourceBracket h2p (sourceAngularEtaRemainderCauchyCandidate hp hp1 m s (c m) r R z₀ ρ)
      (sourceComplexAction hp hp1 k) φ.val =
      (sourcePsiCandidate m (μ,(s m φ.val : Coeff p))-
        I*(2*I*sourceStandardRootOmittedProduct hp hp1 m φ.val μ))*
        sourceDirichletActionKernel hp hp1 m k ch φ.val := by
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
  let v := sourceDirichletActionKernel hp hp1 m k ch φ.val
  let h := sourceHamiltonianVector h2p (sourceComplexAction hp hp1 k) φ.val
  have hiso : SourceIsospectralDirection hp φ.val h :=
    sourceHamiltonianVector_action_isospectral hp hp1 h2p φ.val φ.property k
  have hterminal : μ φ.val ∈ ball (c m) ρ :=
    ball_subset_ball hrρ.le (D.terminal_enclosed φ.val hφ)
  have hflow := D.terminal_action_flow h2p k ch φ hφ hφch
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
  rw [← fderiv_apply_sourceHamiltonianVector]
  change (fderiv ℂ (sourceAngularEtaRemainderCauchyCandidate hp hp1 m s (c m) r R z₀ ρ) φ.val) h = _
  rw [hresult]
  change K φ.val*(sourcePsiCandidate m (μ φ.val,(s m φ.val : Coeff p))/K φ.val-I)*v = _
  field_simp [hKne]
  dsimp only [K,P,sourceStandardRootOmittedJointProduct,μ,v]
  ring

end SourceAngularJointAnnulusChartData
namespace SourceAngularEtaAnalyticChartData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {m : ℤ}
  {s : (j : ℤ) → CoeffPair p → DeletedCoeff p j}
  {W V U : Set (CoeffPair p)} {c : ℤ → ℂ} {T : ℤ → ℝ}
  {r R ρ : ℝ} {z₀ : ℂ} {δ ε : CoeffPair p → ℂ}

/-- Both moving terminal equations determine the actual model angle's
action velocity, including either periodic Dirichlet endpoint. -/
theorem fderiv_modelAngle_action_eq_kernel
    (D : SourceAngularEtaAnalyticChartData hp hp1 m s W V U c T r R z₀ ρ δ ε)
    (h2p : (2 : ℝ≥0∞) ≤ p) (k : ℤ) (ch : SourceRealActionBallChart hp hp1 k)
    (φ : realTypeSourceLocus p) (hφ : φ.val ∈ U) (hφch : φ.val ∈ ball ch.center ch.radius) :
    let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val m
    (fderiv ℂ ε φ.val) (sourceHamiltonianVector h2p (sourceComplexAction hp hp1 k) φ.val) =
      I*(2*I*sourceStandardRootOmittedProduct hp hp1 m φ.val μ)*sourceDirichletActionKernel hp hp1 m k ch φ.val := by
  dsimp only
  let μ : CoeffPair p → ℂ := fun ψ => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m
  let S := sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet m
  let P : ℂ × CoeffPair p → ℂ := fun t => 2*I*sourceStandardRootOmittedJointProduct hp hp1 m t
  let K : CoeffPair p → ℂ := fun ψ => P (μ ψ,ψ)
  let K' := deriv (fun z => P (z,φ.val)) (μ φ.val)
  let M : CoeffPair p → ℂ := fun ψ => sourceStandardRootMidpoint hp hp1 ψ m
  let G := (canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) m)^2
  let Q := (μ φ.val-M φ.val)^2-G/4
  let v := sourceDirichletActionKernel hp hp1 m k ch φ.val
  let h := sourceHamiltonianVector h2p (sourceComplexAction hp hp1 k) φ.val
  have hiso : SourceIsospectralDirection hp φ.val h :=
    sourceHamiltonianVector_action_isospectral hp hp1 h2p φ.val φ.property k
  have hφV := D.angle.source_subset hφ
  have hflow := D.annulus.terminal_action_flow h2p k ch φ hφV hφch
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

/-- The single eta cotangent has the actual normalized action kernel
on every open-gap chart, including periodic Dirichlet endpoints. -/
theorem sourceBivector_etaDifferential_action_eq_kernel
    (D : SourceAngularEtaAnalyticChartData hp hp1 m s W V U c T r R z₀ ρ δ ε)
    {W₀ : Set (CoeffPair p)} (hs : SourcePsiIsolatingComplexExtension hp hp1 W₀ s)
    (h2p : (2 : ℝ≥0∞) ≤ p) (k : ℤ) (ch : SourceRealActionBallChart hp hp1 k)
    (φ : realTypeSourceLocus p) (hφ : φ.val ∈ U) (hφ₀ : φ.val ∈ W₀)
    (hφch : φ.val ∈ ball ch.center ch.radius) :
    let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val m
    sourceBivector h2p (sourceAngularEtaDifferential hp hp1 m s φ.val)
      (fderiv ℂ (sourceComplexAction hp hp1 k) φ.val) =
      sourcePsiCandidate m (μ,(s m φ.val : Coeff p))*sourceDirichletActionKernel hp hp1 m k ch φ.val := by
  dsimp only
  rw [D.etaDifferential_eq_fderiv_representative φ.val hφ]
  have hε := (D.angle.angle_analytic φ.val hφ).differentiableAt
  have hμ := analyticAt_canonicalPeriodOneBoundaryRoots_of_realType hp hp1 .dirichlet φ.val φ.property m
  have hR := (D.annulus.analyticAt_etaRemainderCauchyCandidate ρ D.inner_lt_cauchy D.cauchy_lt_outer
    φ.val (D.angle.source_subset hφ) hμ).differentiableAt
  have hd := ((hε.hasFDerivAt.sub_const (Real.pi : ℂ)).fun_add hR.hasFDerivAt).fderiv
  change fderiv ℂ (sourceAngularEtaCauchyRepresentative hp hp1 m s (c m) r R z₀ ρ ε) φ.val = _ at hd
  rw [hd]
  simp only [map_add,add_apply]
  have hmodel := D.fderiv_modelAngle_action_eq_kernel h2p k ch φ hφ hφch
  have hrem := D.annulus.sourceBracket_etaRemainder_action_eq_kernel hs h2p k ρ D.inner_lt_cauchy D.cauchy_lt_outer
    ch φ (D.angle.source_subset hφ) hφ₀ hφch
  rw [fderiv_apply_sourceHamiltonianVector] at hmodel
  dsimp only at hmodel hrem
  change sourceBracket h2p ε (sourceComplexAction hp hp1 k) φ.val+
    sourceBracket h2p (sourceAngularEtaRemainderCauchyCandidate hp hp1 m s (c m) r R z₀ ρ)
      (sourceComplexAction hp hp1 k) φ.val = _
  linear_combination hmodel+hrem

end SourceAngularEtaAnalyticChartData

/-- The normalized contribution of every Dirichlet terminal to an
actual theta/action bracket, including the diagonal terminal. -/
def sourceAngularActionKernelTerm (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n k : ℤ) (ch : SourceRealActionBallChart hp hp1 k)
    (s : (j : ℤ) → CoeffPair p → DeletedCoeff p j) (φ : CoeffPair p) (m : ℤ) : ℂ :=
  sourcePsiCandidate n (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ m,(s n φ : Coeff p))*
    sourceDirichletActionKernel hp hp1 m k ch φ

/-- Adding the proved diagonal eta kernel gives the actual theta/action
bracket as the limit of one full symmetric normalized kernel sum. -/
theorem SourceAngularThetaCommonDomainData.tendsto_full_thetaActionKernels_on_chart
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
    {s : (j : ℤ) → CoeffPair p → DeletedCoeff p j}
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (h2p : (2 : ℝ≥0∞) ≤ p) (n k : ℤ)
    {V U : Set (CoeffPair p)} {c : ℤ → ℂ} {T : ℤ → ℝ}
    {r R ρ : ℝ} {z₀ : ℂ} {δ ε : CoeffPair p → ℂ}
    (C : SourceAngularEtaAnalyticChartData hp hp1 n s B V U c T r R z₀ ρ δ ε)
    (hUW : U ⊆ W) (ch : SourceRealActionBallChart hp hp1 k)
    (φ : realTypeSourceLocus p) (hφ : φ.val ∈ U) (hφch : φ.val ∈ ball ch.center ch.radius) :
    Tendsto (fun N : ℕ => ∑ m ∈ Finset.Icc (-(N : ℤ)) N,
      sourceAngularActionKernelTerm hp hp1 n k ch s φ.val m) atTop
      (𝓝 (sourceAngularThetaFunctionalBracket hp hp1 h2p n s (sourceComplexAction hp hp1 k) φ.val)) := by
  have hs := D.psi.toSourcePsiIsolatingComplexExtension
  obtain ⟨a,ha,_,_,_,_,hball,_,_,_,_⟩ := hs.isolation φ
  have hφ₀ : φ.val ∈ W₀ := hball (mem_ball_self ha)
  have ht := D.tendsto_thetaActionKernels h2p n k C hUW ch φ hφ hφch
  have he := C.sourceBivector_etaDifferential_action_eq_kernel hs h2p k ch φ hφ hφ₀ hφch
  dsimp only at he
  rw [he] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop n.natAbs] with N hN
  let F : ℤ → ℂ := sourceAngularActionKernelTerm hp hp1 n k ch s φ.val
  change F n+∑ m ∈ Finset.Icc (-(N : ℤ)) N, (if m = n then 0 else F m) =
    ∑ m ∈ Finset.Icc (-(N : ℤ)) N, F m
  have hmem : n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
    simp only [Finset.mem_Icc]
    omega
  have hdiag : (∑ m ∈ Finset.Icc (-(N : ℤ)) N, if m = n then F m else 0) = F n := by
    simp [hmem]
  rw [← hdiag,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _
  by_cases hmn : m = n <;> simp [hmn]

/-- Actual common-domain eta charts are constructed at every open real
gap, so the full normalized sum requires no supplied angular chart. -/
theorem SourceAngularThetaCommonDomainData.tendsto_thetaActionKernelSum
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
    {s : (j : ℤ) → CoeffPair p → DeletedCoeff p j}
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (h2p : (2 : ℝ≥0∞) ≤ p) (n k : ℤ)
    (ch : SourceRealActionBallChart hp hp1 k) (φ : realTypeSourceLocus p)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0)
    (hφch : φ.val ∈ ball ch.center ch.radius) :
    Tendsto (fun N : ℕ => ∑ m ∈ Finset.Icc (-(N : ℤ)) N,
      sourceAngularActionKernelTerm hp hp1 n k ch s φ.val m) atTop
      (𝓝 (sourceAngularThetaFunctionalBracket hp hp1 h2p n s (sourceComplexAction hp hp1 k) φ.val)) := by
  obtain ⟨V,U,c,T,r,R,z₀,ρ,δ,ε,hφU,hUW,_,C⟩ := D.local_charts n φ.val (D.real_subset φ.property) hgap
  exact D.tendsto_full_thetaActionKernels_on_chart h2p n k C hUW ch φ hφU hφch

end NLS.ZakharovShabat
