import NLS.ZakharovShabat.SourceDirichletActionKernel
import NLS.ZakharovShabat.SourceAngularBetaIsospectral
import NLS.ZakharovShabat.SourceAngularBetaSeriesDifferential

/-! # Actual beta/action kernels at every Dirichlet terminal

The full moving terminal flow and stationarity of the interior Cauchy
primitive determine the beta/action bracket without dividing by the
terminal anti-discriminant. Periodic terminals and collapsed selected
gaps therefore have the same normalized contour kernel.
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

/-- The spectral derivative of the actual discriminant factorization
inside the selected disc, including its periodic endpoints. -/
theorem discriminant_mul_deriv_eq_omittedProduct
    (D : SourceAngularJointAnnulusChartData hp hp1 m s W V c T r R z₀)
    (φ : CoeffPair p) (hφ : φ ∈ V) (z : ℂ) (hz : z ∈ ball (c m) (T m)) :
    let P : ℂ → ℂ := fun w => 2*I*sourceStandardRootOmittedProduct hp hp1 m φ w
    let M := sourceStandardRootMidpoint hp hp1 φ m
    let G := (canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) m)^2
    canonicalDiscriminant hp (periodOnePotential φ) z*
      deriv (canonicalDiscriminant hp (periodOnePotential φ)) z =
      P z*deriv P z*((z-M)^2-G/4)+P z^2*(z-M) := by
  dsimp only
  let P : ℂ → ℂ := fun w => 2*I*sourceStandardRootOmittedProduct hp hp1 m φ w
  let M := sourceStandardRootMidpoint hp hp1 φ m
  let G := (canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) m)^2
  have hP : DifferentiableAt ℂ P z := by
    exact ((analyticAt_const.mul (D.omitted_analytic (z,φ) ⟨hz,hφ⟩)).comp
      (f := fun w : ℂ => (w,φ)) (analyticAt_id.prod analyticAt_const)).differentiableAt
  have hΔ := (analyticOnNhd_canonicalDiscriminant hp hp1
    (periodOnePotential φ) (periodOnePotential_mem φ) z (mem_univ _)).differentiableAt.hasDerivAt
  have hQ := hasDerivAt_quadraticRootPolynomial M (G/4) z
  have hfactor : (fun w => (canonicalDiscriminant hp (periodOnePotential φ) w)^2-4) =ᶠ[𝓝 z]
      (fun w => P w^2*quadraticRootPolynomial M (G/4) w) := by
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw
    have hother : w ∈ sourceStandardRootOmittedDomain hp hp1 φ m :=
      ((D.disc_family φ hφ).contour_family.2 m).2.2.1 (ball_subset_closedBall hw)
    dsimp only [P,quadraticRootPolynomial,M,G,sourceStandardRootMidpoint]
    rw [canonicalDiscriminant_sq_sub_four_eq_midpoint_mul hp hp1 _ (periodOnePotential_mem φ) m,
      ← sourceStandardRootOmittedProduct_sq_eq_canonicalDeletedPeriodicProduct hp hp1 φ m w hother]
    simp only [mul_pow,I_sq]
    ring
  have hd := (hΔ.pow 2).sub_const (4 : ℂ)
  have hpq := (hP.hasDerivAt.pow 2).fun_mul hQ
  simp only [Pi.pow_apply] at hd hpq
  have he := hfactor.deriv_eq
  rw [hd.deriv,hpq.deriv] at he
  dsimp only [quadraticRootPolynomial] at he
  linear_combination he/2

/-- Every actual off-diagonal beta/action bracket is the normalized
numerator times the common action contour kernel. No regular-terminal
or nonzero-gap premise occurs. -/
theorem sourceBracket_beta_action_eq_kernel
    (D : SourceAngularJointAnnulusChartData hp hp1 m s W V c T r R z₀)
    {W₀ : Set (CoeffPair p)} (hs : SourcePsiIsolatingComplexExtension hp hp1 W₀ s)
    (h2p : (2 : ℝ≥0∞) ≤ p) (n k : ℤ) (hmn : m ≠ n)
    (ch : SourceRealActionBallChart hp hp1 k) (φ : realTypeSourceLocus p)
    (hφ : φ.val ∈ V) (hφ₀ : φ.val ∈ W₀) (hφch : φ.val ∈ ball ch.center ch.radius) :
    let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val m
    sourceBracket h2p (sourceAngularBeta hp hp1 n m s) (sourceComplexAction hp hp1 k) φ.val =
      sourcePsiCandidate n (μ,(s n φ.val : Coeff p))*sourceDirichletActionKernel hp hp1 m k ch φ.val := by
  dsimp only
  let ρ := (r+R)/2
  have hrρ : r < ρ := by dsimp only [ρ]; linarith [D.inner_lt_outer]
  have hρR : ρ < R := by dsimp only [ρ]; linarith [D.inner_lt_outer]
  let μ : CoeffPair p → ℂ := fun ψ => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m
  let δ := sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet m
  let P : ℂ × CoeffPair p → ℂ := fun t => 2*I*sourceStandardRootOmittedJointProduct hp hp1 m t
  let K : CoeffPair p → ℂ := fun ψ => P (μ ψ,ψ)
  let K' := deriv (fun z => P (z,φ.val)) (μ φ.val)
  let M := sourceStandardRootMidpoint hp hp1 φ.val m
  let G := (canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) m)^2
  let Q := (μ φ.val-M)^2-G/4
  let H := sourceAngularQuotientCauchyCandidate hp hp1 n m s (c m) r R z₀ ρ
  let v := sourceDirichletActionKernel hp hp1 m k ch φ.val
  let h := sourceHamiltonianVector h2p (sourceComplexAction hp hp1 k) φ.val
  have hiso : SourceIsospectralDirection hp φ.val h :=
    sourceHamiltonianVector_action_isospectral hp hp1 h2p φ.val φ.property k
  have hμ : DifferentiableAt ℂ μ φ.val :=
    (analyticAt_canonicalPeriodOneBoundaryRoots_of_realType hp hp1 .dirichlet φ.val φ.property m).differentiableAt
  have hterminal : μ φ.val ∈ ball (c m) ρ :=
    ball_subset_ball hrρ.le (D.terminal_enclosed φ.val hφ)
  have hterminalT : μ φ.val ∈ ball (c m) (T m) :=
    (D.disc_family φ.val hφ).dirichlet_mem_ball m
  have hother : μ φ.val ∈ sourceStandardRootOmittedDomain hp hp1 φ.val m :=
    ((D.disc_family φ.val hφ).contour_family.2 m).2.2.1 (ball_subset_closedBall hterminalT)
  have hKne : K φ.val ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) I_ne_zero)
      (sourceStandardRootOmittedProduct_ne_zero hp hp1 φ.val (μ φ.val) m hother)
  have hPjoint : DifferentiableAt ℂ P (μ φ.val,φ.val) :=
    (analyticAt_const.mul (D.omitted_analytic (μ φ.val,φ.val) ⟨hterminalT,hφ⟩)).differentiableAt
  have hroot := sourceBracket_dirichletRoot_action_eq_kernel hp hp1 h2p m k ch φ.val φ.property hφch
  rw [← fderiv_apply_sourceHamiltonianVector] at hroot
  change (fderiv ℂ μ φ.val) h = δ φ.val*v at hroot
  have hanti := sourceBracket_dirichletTerminalAnti_action_eq_kernel hp hp1 h2p m k ch φ.val φ.property hφch
  rw [← fderiv_apply_sourceHamiltonianVector] at hanti
  dsimp only at hanti
  have hf := D.discriminant_mul_deriv_eq_omittedProduct φ.val hφ (μ φ.val) hterminalT
  change canonicalDiscriminant hp (periodOnePotential φ.val) (μ φ.val)*
      deriv (canonicalDiscriminant hp (periodOnePotential φ.val)) (μ φ.val) =
    K φ.val*K'*Q+K φ.val^2*(μ φ.val-M) at hf
  rw [hf] at hanti
  change (fderiv ℂ δ φ.val) h = (K φ.val*K'*Q+K φ.val^2*(μ φ.val-M))*v at hanti
  have hPsource : (fderiv ℂ (fun ψ => P (μ φ.val,ψ)) φ.val) h = 0 := by
    have ho := ((D.omitted_analytic (μ φ.val,φ.val) ⟨hterminalT,hφ⟩).comp
      (f := fun ψ : CoeffPair p => (μ φ.val,ψ)) (analyticAt_const.prod analyticAt_id)).differentiableAt
    change DifferentiableAt ℂ (fun ψ : CoeffPair p => sourceStandardRootOmittedProduct hp hp1 m ψ (μ φ.val)) φ.val at ho
    change (fderiv ℂ (fun ψ : CoeffPair p => 2*I*sourceStandardRootOmittedProduct hp hp1 m ψ (μ φ.val)) φ.val) h = 0
    rw [(ho.hasFDerivAt.const_mul (2*I)).fderiv]
    simp only [smul_apply,smul_eq_mul,
      fderiv_sourceStandardRootOmittedProduct_isospectral_eq_zero hp hp1 φ.val φ.property h hiso m (μ φ.val) hother,mul_zero]
  have hKflow : (fderiv ℂ K φ.val) h = K'*δ φ.val*v := by
    rw [fderiv_moving_spectral_parameter P μ φ.val hPjoint hμ]
    simp only [add_apply,smul_apply,smul_eq_mul,hPsource,zero_add,hroot]
    ring
  have hsq : δ φ.val^2 = K φ.val^2*Q := by
    dsimp only [δ,sourceBoundaryTerminalAntiDiscriminant,K,P,sourceStandardRootOmittedJointProduct,Q,M,G,μ,sourceStandardRootMidpoint]
    rw [← sourceDiscriminant_sq_sub_four_at_canonicalDirichletRoot hp hp1 φ.val m,
      canonicalDiscriminant_sq_sub_four_eq_midpoint_mul hp hp1 _ (periodOnePotential_mem φ.val) m,
      ← sourceStandardRootOmittedProduct_sq_eq_canonicalDeletedPeriodicProduct hp hp1 φ.val m _ hother]
    simp only [mul_pow,I_sq]
    ring
  have hbeta := D.fderiv_beta_isospectral_terminal_eq hs n hmn ρ hrρ hρR φ hφ hφ₀ h hiso
  change K φ.val^2*(fderiv ℂ (sourceAngularBeta hp hp1 n m s) φ.val) h =
    ((fderiv ℂ δ φ.val) h*K φ.val-δ φ.val*(fderiv ℂ K φ.val) h)*H (μ φ.val,φ.val)+
      δ φ.val*K φ.val*deriv (fun z => H (z,φ.val)) (μ φ.val)*(fderiv ℂ μ φ.val) h at hbeta
  rw [hroot] at hbeta
  have heq := D.quotientCauchyCandidate_equation φ.val hφ n hmn ρ hrρ hρR (μ φ.val) hterminal
  have hresult := quadratic_sheet_terminal_variation_of_flow (δ φ.val) (K φ.val) Q
    (μ φ.val-M) (H (μ φ.val,φ.val)) (deriv (fun z => H (z,φ.val)) (μ φ.val))
    (sourceAngularGapNumerator hp hp1 n m s φ.val (μ φ.val)) v K'
    ((fderiv ℂ δ φ.val) h) ((fderiv ℂ K φ.val) h)
    ((fderiv ℂ (sourceAngularBeta hp hp1 n m s) φ.val) h) hKne hsq hanti hKflow heq hbeta
  rw [← fderiv_apply_sourceHamiltonianVector]
  change (fderiv ℂ (sourceAngularBeta hp hp1 n m s) φ.val) h = _
  rw [hresult]
  change K φ.val*(sourcePsiCandidate n (μ φ.val,(s n φ.val : Coeff p))/K φ.val)*v = _
  field_simp [hKne]
  rfl

end SourceAngularJointAnnulusChartData

/-- Local actual annuli exist at every real source, so no angular chart
is an extra hypothesis in the actual beta/action kernel formula. -/
theorem SourcePsiIsolatingComplexExtension.sourceBracket_beta_action_eq_kernel
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ : Set (CoeffPair p)}
    {s : (j : ℤ) → CoeffPair p → DeletedCoeff p j}
    (hs : SourcePsiIsolatingComplexExtension hp hp1 W₀ s)
    (h2p : (2 : ℝ≥0∞) ≤ p) (n m k : ℤ) (hmn : m ≠ n)
    (ch : SourceRealActionBallChart hp hp1 k) (φ : realTypeSourceLocus p)
    (hφch : φ.val ∈ ball ch.center ch.radius) :
    let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val m
    sourceBracket h2p (sourceAngularBeta hp hp1 n m s) (sourceComplexAction hp hp1 k) φ.val =
      sourcePsiCandidate n (μ,(s n φ.val : Coeff p))*sourceDirichletActionKernel hp hp1 m k ch φ.val := by
  obtain ⟨a,ha,_,_,_,_,hball,_,_,_,_⟩ := hs.isolation φ
  obtain ⟨A,hA,_,hAreal,hMG⟩ := exists_global_source_analytic_midpoint_squaredGap hp hp1
  let O := ball φ.val a ∩ A
  have hO : IsOpen O := isOpen_ball.inter hA
  have hOW₀ : O ⊆ W₀ := fun ψ hψ => hball hψ.1
  have hφO : φ.val ∈ O := ⟨mem_ball_self ha,hAreal φ.property⟩
  obtain ⟨V,c,T,r,R,z₀,hφV,D⟩ := hs.exists_local_joint_angular_annulus_primitives
    O hO hOW₀ (fun ψ hψ => hMG ψ hψ.2) φ.val hφO φ.property m
  exact D.sourceBracket_beta_action_eq_kernel hs h2p n k hmn ch φ hφV
    (hball (mem_ball_self ha)) hφch

/-- The actual normalized off-diagonal action contribution, with the
same omitted diagonal as the actual beta correction series. -/
def sourceAngularBetaActionKernelTerm (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n k : ℤ) (ch : SourceRealActionBallChart hp hp1 k)
    (s : (j : ℤ) → CoeffPair p → DeletedCoeff p j) (φ : CoeffPair p) (m : ℤ) : ℂ :=
  if m = n then 0 else
    sourcePsiCandidate n (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ m,(s n φ : Coeff p))*
      sourceDirichletActionKernel hp hp1 m k ch φ

/-- The full actual beta correction/action bracket is the limit of
the normalized kernel cutoffs, also when selected gaps are collapsed
or their Dirichlet roots lie at periodic endpoints. -/
theorem SourceAngularThetaCommonDomainData.tendsto_betaActionKernels
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
    {s : (j : ℤ) → CoeffPair p → DeletedCoeff p j}
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (h2p : (2 : ℝ≥0∞) ≤ p) (n k : ℤ)
    (ch : SourceRealActionBallChart hp hp1 k) (φ : realTypeSourceLocus p)
    (hφch : φ.val ∈ ball ch.center ch.radius) :
    Tendsto (fun N : ℕ => ∑ m ∈ Finset.Icc (-(N : ℤ)) N,
      sourceAngularBetaActionKernelTerm hp hp1 n k ch s φ.val m) atTop
      (𝓝 (sourceBracket h2p (sourceAngularBetaCorrection hp hp1 n s)
        (sourceComplexAction hp hp1 k) φ.val)) := by
  apply (D.tendsto_betaSeriesBrackets h2p n (sourceComplexAction hp hp1 k)
    φ.val (D.real_subset φ.property)).congr'
  apply Eventually.of_forall
  intro N
  apply Finset.sum_congr rfl
  intro m _
  by_cases hmn : m = n
  · simp [sourceAngularBetaSeriesTerm,sourceAngularBetaActionKernelTerm,hmn,sourceBracket]
  · simpa only [sourceAngularBetaSeriesTerm,sourceAngularBetaActionKernelTerm,if_neg hmn] using
      D.psi.toSourcePsiIsolatingComplexExtension.sourceBracket_beta_action_eq_kernel
        h2p n m k hmn ch φ hφch

/-- The actual theta/action bracket is the limit of its diagonal eta
contribution plus the normalized off-diagonal action kernel cutoffs. -/
theorem SourceAngularThetaCommonDomainData.tendsto_thetaActionKernels
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
    {s : (j : ℤ) → CoeffPair p → DeletedCoeff p j}
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (h2p : (2 : ℝ≥0∞) ≤ p) (n k : ℤ)
    {V U : Set (CoeffPair p)} {c : ℤ → ℂ} {T : ℤ → ℝ}
    {r R ρ : ℝ} {z₀ : ℂ} {δ ε : CoeffPair p → ℂ}
    (C : SourceAngularEtaAnalyticChartData hp hp1 n s B V U c T r R z₀ ρ δ ε)
    (hUW : U ⊆ W) (ch : SourceRealActionBallChart hp hp1 k)
    (φ : realTypeSourceLocus p) (hφ : φ.val ∈ U)
    (hφch : φ.val ∈ ball ch.center ch.radius) :
    Tendsto (fun N : ℕ => sourceBivector h2p (sourceAngularEtaDifferential hp hp1 n s φ.val)
      (fderiv ℂ (sourceComplexAction hp hp1 k) φ.val)+
      ∑ m ∈ Finset.Icc (-(N : ℤ)) N, sourceAngularBetaActionKernelTerm hp hp1 n k ch s φ.val m) atTop
      (𝓝 (sourceAngularThetaFunctionalBracket hp hp1 h2p n s (sourceComplexAction hp hp1 k) φ.val)) := by
  have ht := (tendsto_const_nhds (x := sourceBivector h2p
    (sourceAngularEtaDifferential hp hp1 n s φ.val)
    (fderiv ℂ (sourceComplexAction hp hp1 k) φ.val))).add
      (D.tendsto_betaActionKernels h2p n k ch φ hφch)
  have heq : sourceAngularThetaFunctionalBracket hp hp1 h2p n s (sourceComplexAction hp hp1 k) φ.val =
      sourceBivector h2p (sourceAngularEtaDifferential hp hp1 n s φ.val)
        (fderiv ℂ (sourceComplexAction hp hp1 k) φ.val)+
      sourceBracket h2p (sourceAngularBetaCorrection hp hp1 n s) (sourceComplexAction hp hp1 k) φ.val := by
    rw [sourceAngularThetaFunctionalBracket,C.thetaDifferential_eq_eta_add_betaCorrection
      ((D.beta_series.analytic_correction n).mono (hUW.trans D.source_subset)) φ.val hφ]
    simp only [map_add,add_apply,sourceBracket]
  rw [← heq] at ht
  exact ht

end NLS.ZakharovShabat
