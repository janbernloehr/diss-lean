import NLS.ZakharovShabat.SourceAngularTerminalIsospectralFlow
import NLS.ZakharovShabat.SourceAngularBetaIsospectral
import NLS.ZakharovShabat.SourceDirichletDiscriminantKernel
import NLS.ZakharovShabat.SourceAngularBetaSeriesDifferential

/-! # Actual beta/discriminant kernels through every terminal

The actual full isospectral sheet flow differentiates beta without
any division by the terminal square root. The filled discriminant
kernel covers coincident parameters, periodic terminals and collapsed gaps.
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

/-- The actual beta derivative in any isospectral sheet flow is the
normalized numerator times its common terminal velocity coefficient. -/
theorem fderiv_beta_isospectral_eq_kernel
    (D : SourceAngularJointAnnulusChartData hp hp1 m s W V c T r R z₀)
    {W₀ : Set (CoeffPair p)} (hs : SourcePsiIsolatingComplexExtension hp hp1 W₀ s)
    (n : ℤ) (hmn : m ≠ n) (φ : realTypeSourceLocus p)
    (hφ : φ.val ∈ V) (hφ₀ : φ.val ∈ W₀)
    (h : CoeffPair p) (hiso : SourceIsospectralDirection hp φ.val h) (v : ℂ)
    (hroot₀ : (fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m) φ.val) h =
      sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet m φ.val*v)
    (hanti₀ : (fderiv ℂ (sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet m) φ.val) h =
      let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val m
      canonicalDiscriminant hp (periodOnePotential φ.val) μ*
        deriv (canonicalDiscriminant hp (periodOnePotential φ.val)) μ*v) :
    let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val m
    (fderiv ℂ (sourceAngularBeta hp hp1 n m s) φ.val) h =
      sourcePsiCandidate n (μ,(s n φ.val : Coeff p))*v := by
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
  have hterminal : μ φ.val ∈ ball (c m) ρ :=
    ball_subset_ball hrρ.le (D.terminal_enclosed φ.val hφ)
  have hflow := D.terminal_isospectral_flow φ hφ h hiso v hroot₀ hanti₀
  change K φ.val ≠ 0 ∧ (fderiv ℂ μ φ.val) h = δ φ.val*v ∧
      (fderiv ℂ δ φ.val) h = (K φ.val*K'*Q+K φ.val^2*(μ φ.val-M))*v ∧
      (fderiv ℂ K φ.val) h = K'*δ φ.val*v ∧ δ φ.val^2 = K φ.val^2*Q at hflow
  obtain ⟨hKne,hroot,hanti,hKflow,hsq⟩ := hflow
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
  change (fderiv ℂ (sourceAngularBeta hp hp1 n m s) φ.val) h = _
  rw [hresult]
  change K φ.val*(sourcePsiCandidate n (μ φ.val,(s n φ.val : Coeff p))/K φ.val)*v = _
  field_simp [hKne]
  dsimp only [μ]
  ring


end SourceAngularJointAnnulusChartData

/-- Every actual off-diagonal beta has the filled discriminant kernel
at every real source, without a supplied angular chart or open-gap premise. -/
theorem SourcePsiIsolatingComplexExtension.sourceBracket_beta_discriminant_eq_kernel
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ : Set (CoeffPair p)}
    {s : (j : ℤ) → CoeffPair p → DeletedCoeff p j}
    (hs : SourcePsiIsolatingComplexExtension hp hp1 W₀ s)
    (h2p : (2 : ℝ≥0∞) ≤ p) (n m : ℤ) (hmn : m ≠ n)
    (φ : realTypeSourceLocus p) (w : ℂ) :
    let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val m
    sourceBracket h2p (sourceAngularBeta hp hp1 n m s)
      (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ) w) φ.val =
      sourcePsiCandidate n (μ,(s n φ.val : Coeff p))*sourceDirichletDiscriminantKernel hp hp1 m φ.val w := by
  obtain ⟨a,ha,_,_,_,_,hball,_,_,_,_⟩ := hs.isolation φ
  obtain ⟨A,hA,_,hAreal,hMG⟩ := exists_global_source_analytic_midpoint_squaredGap hp hp1
  let O := ball φ.val a ∩ A
  have hO : IsOpen O := isOpen_ball.inter hA
  have hOW₀ : O ⊆ W₀ := fun ψ hψ => hball hψ.1
  have hφO : φ.val ∈ O := ⟨mem_ball_self ha,hAreal φ.property⟩
  obtain ⟨V,c,T,r,R,z₀,hφV,D⟩ := hs.exists_local_joint_angular_annulus_primitives
    O hO hOW₀ (fun ψ hψ => hMG ψ hψ.2) φ.val hφO φ.property m
  let h := sourceHamiltonianVector h2p
    (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ) w) φ.val
  have hiso : SourceIsospectralDirection hp φ.val h :=
    sourceHamiltonianVector_discriminant_isospectral hp hp1 h2p φ.val w
  have hroot := sourceBracket_dirichletRoot_discriminant_eq_kernel hp hp1 h2p m φ.val φ.property w
  have hanti := sourceBracket_dirichletTerminalAnti_discriminant_eq_kernel hp hp1 h2p m φ.val φ.property w
  rw [← fderiv_apply_sourceHamiltonianVector] at hroot hanti
  rw [← fderiv_apply_sourceHamiltonianVector]
  exact D.fderiv_beta_isospectral_eq_kernel hs n hmn φ hφV (hball (mem_ball_self ha))
    h hiso (sourceDirichletDiscriminantKernel hp hp1 m φ.val w) hroot hanti

/-- The actual off-diagonal contribution uses the same omitted
diagonal as the full beta correction series. -/
def sourceAngularBetaDiscriminantKernelTerm (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (s : (j : ℤ) → CoeffPair p → DeletedCoeff p j) (φ : CoeffPair p) (w : ℂ) (m : ℤ) : ℂ :=
  if m = n then 0 else
    sourcePsiCandidate n (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ m,(s n φ : Coeff p))*
      sourceDirichletDiscriminantKernel hp hp1 m φ w

/-- The full actual beta/discriminant bracket is the limit of its
filled symmetric terminal kernel sums at every spectral parameter. -/
theorem SourceAngularThetaCommonDomainData.tendsto_betaDiscriminantKernels
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
    {s : (j : ℤ) → CoeffPair p → DeletedCoeff p j}
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (h2p : (2 : ℝ≥0∞) ≤ p) (n : ℤ) (φ : realTypeSourceLocus p) (w : ℂ) :
    Tendsto (fun N : ℕ => ∑ m ∈ Finset.Icc (-(N : ℤ)) N,
      sourceAngularBetaDiscriminantKernelTerm hp hp1 n s φ.val w m) atTop
      (𝓝 (sourceBracket h2p (sourceAngularBetaCorrection hp hp1 n s)
        (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ) w) φ.val)) := by
  apply (D.tendsto_betaSeriesBrackets h2p n
    (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ) w)
    φ.val (D.real_subset φ.property)).congr'
  apply Eventually.of_forall
  intro N
  apply Finset.sum_congr rfl
  intro m _
  by_cases hmn : m = n
  · simp [sourceAngularBetaSeriesTerm,sourceAngularBetaDiscriminantKernelTerm,hmn,sourceBracket]
  · simpa only [sourceAngularBetaSeriesTerm,sourceAngularBetaDiscriminantKernelTerm,if_neg hmn] using
      D.psi.toSourcePsiIsolatingComplexExtension.sourceBracket_beta_discriminant_eq_kernel
        h2p n m hmn φ w

end NLS.ZakharovShabat
