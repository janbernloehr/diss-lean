import NLS.ComplexAnalysis.QuadraticSheetTerminalVariation
import NLS.ZakharovShabat.SourceAngularCauchyIsospectral
import NLS.ZakharovShabat.SourceAngularBetaCauchyAnalytic
import NLS.ZakharovShabat.SourceBoundaryTerminalDifferential

/-! # The actual moving beta variation in isospectral directions

The actual beta is the terminal value of its interior Cauchy candidate.
Differentiate this value and the exact quadratic-sheet identity. The
omitted-product derivative cancels, and the stationary symmetric data
and interior primitive leave the actual normalized numerator times the
moving root variation. The cleared equation includes branch terminals.
-/

noncomputable section
set_option maxHeartbeats 800000
open Set Metric Complex Filter Topology NLS.ComplexAnalysis NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

namespace SourceAngularJointAnnulusChartData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {m : ℤ}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}
  {W V : Set (CoeffPair p)} {c : ℤ → ℂ} {T : ℤ → ℝ} {r R : ℝ} {z₀ : ℂ}

/-- Differentiating the actual terminal quotient retains the full
moving omitted-product derivative. Only the interior primitive is
stationary in an isospectral direction. -/
theorem fderiv_beta_isospectral_terminal_eq
    (D : SourceAngularJointAnnulusChartData hp hp1 m s W V c T r R z₀)
    {W₀ : Set (CoeffPair p)} (hs : SourcePsiIsolatingComplexExtension hp hp1 W₀ s)
    (n : ℤ) (hmn : m ≠ n) (ρ : ℝ) (hrρ : r < ρ) (hρR : ρ < R)
    (φ : realTypeSourceLocus p) (hφ : φ.val ∈ V) (hφ₀ : φ.val ∈ W₀)
    (h : CoeffPair p) (hiso : SourceIsospectralDirection hp φ.val h) :
    let μ : CoeffPair p → ℂ := fun ψ => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m
    let δ := sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet m
    let H := sourceAngularQuotientCauchyCandidate hp hp1 n m s (c m) r R z₀ ρ
    let K : CoeffPair p → ℂ := fun ψ => 2*I*sourceStandardRootOmittedJointProduct hp hp1 m (μ ψ,ψ)
    K φ.val^2*(fderiv ℂ (sourceAngularBeta hp hp1 n m s) φ.val) h =
      ((fderiv ℂ δ φ.val) h*K φ.val-δ φ.val*(fderiv ℂ K φ.val) h)*H (μ φ.val,φ.val)+
        δ φ.val*K φ.val*deriv (fun z => H (z,φ.val)) (μ φ.val)*(fderiv ℂ μ φ.val) h := by
  dsimp only
  let μ : CoeffPair p → ℂ := fun ψ => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m
  let δ := sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet m
  let H := sourceAngularQuotientCauchyCandidate hp hp1 n m s (c m) r R z₀ ρ
  let P : ℂ × CoeffPair p → ℂ := fun t => 2*I*sourceStandardRootOmittedJointProduct hp hp1 m t
  let K : CoeffPair p → ℂ := fun ψ => P (μ ψ,ψ)
  let F : CoeffPair p → ℂ := fun ψ => H (μ ψ,ψ)
  have hμ : DifferentiableAt ℂ μ φ.val :=
    (analyticAt_canonicalPeriodOneBoundaryRoots_of_realType hp hp1 .dirichlet φ.val φ.property m).differentiableAt
  have hδ : DifferentiableAt ℂ δ φ.val :=
    (analyticAt_sourceBoundaryTerminalAntiDiscriminant_of_realType hp hp1 .dirichlet m φ.val φ.property).differentiableAt
  have hterminal : μ φ.val ∈ ball (c m) ρ :=
    ball_subset_ball hrρ.le (D.terminal_enclosed φ.val hφ)
  have hother (ψ : CoeffPair p) (hψ : ψ ∈ V) :
      μ ψ ∈ sourceStandardRootOmittedDomain hp hp1 ψ m :=
    ((D.disc_family ψ hψ).contour_family.2 m).2.2.1
      (ball_subset_closedBall ((D.disc_family ψ hψ).dirichlet_mem_ball m))
  have hKne : K φ.val ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) I_ne_zero)
      (sourceStandardRootOmittedProduct_ne_zero hp hp1 φ.val (μ φ.val) m (hother φ.val hφ))
  have hgraph : AnalyticAt ℂ (fun ψ : CoeffPair p => (μ ψ,ψ)) φ.val :=
    (analyticAt_canonicalPeriodOneBoundaryRoots_of_realType hp hp1 .dirichlet φ.val φ.property m).prod analyticAt_id
  have hK : DifferentiableAt ℂ K φ.val :=
    ((analyticAt_const.mul (D.omitted_analytic (μ φ.val,φ.val)
      ⟨(D.disc_family φ.val hφ).dirichlet_mem_ball m,hφ⟩)).comp
        (f := fun ψ : CoeffPair p => (μ ψ,ψ)) hgraph).differentiableAt
  have hHjoint : DifferentiableAt ℂ H (μ φ.val,φ.val) :=
    (D.analyticOnNhd_quotientCauchyCandidate n ρ hrρ hρR _ ⟨hterminal,hφ⟩).differentiableAt
  have hF : DifferentiableAt ℂ F φ.val :=
    hHjoint.comp φ.val (f := fun ψ : CoeffPair p => (μ ψ,ψ)) hgraph.differentiableAt
  have hFvariation : (fderiv ℂ F φ.val) h =
      deriv (fun z => H (z,φ.val)) (μ φ.val)*(fderiv ℂ μ φ.val) h := by
    rw [fderiv_moving_spectral_parameter H μ φ.val hHjoint hμ]
    simp only [add_apply,smul_apply,smul_eq_mul]
    rw [D.fderiv_quotientCauchyCandidate_isospectral_eq_zero hs n hmn ρ hrρ hρR
      φ hφ hφ₀ h hiso (μ φ.val) hterminal,zero_add]
  let B : CoeffPair p → ℂ := fun ψ => δ ψ*(K ψ)⁻¹*F ψ
  have hBnear : B =ᶠ[𝓝 φ.val] sourceAngularBeta hp hp1 n m s := by
    filter_upwards [D.source_open.mem_nhds hφ] with ψ hψ
    simpa only [B,δ,K,P,F,μ,sourceBoundaryTerminalAntiDiscriminant,
      sourceStandardRootOmittedJointProduct,sourceAngularBetaCauchyCandidate,div_eq_mul_inv] using
      D.betaCauchyCandidate_eq_beta ψ hψ n hmn ρ hrρ hρR
  have hi := (hasFDerivAt_inv hKne).comp φ.val hK.hasFDerivAt
  have hB := (hδ.hasFDerivAt.fun_mul hi).fun_mul hF.hasFDerivAt
  simp only [Function.comp_def] at hB
  have hbeta : K φ.val^2*(fderiv ℂ (sourceAngularBeta hp hp1 n m s) φ.val) h =
      ((fderiv ℂ δ φ.val) h*K φ.val-δ φ.val*(fderiv ℂ K φ.val) h)*F φ.val+
        δ φ.val*K φ.val*deriv (fun z => H (z,φ.val)) (μ φ.val)*(fderiv ℂ μ φ.val) h := by
    rw [← hBnear.fderiv_eq,hB.fderiv]
    simp only [add_apply,smul_apply,smul_eq_mul,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply]
    rw [hFvariation]
    field_simp [hKne]
    ring
  exact hbeta

/-- The actual off-diagonal beta variation, with its terminal square
root retained as a factor. Every real base and collapsed gap is included. -/
theorem fderiv_beta_isospectral_cleared
    (D : SourceAngularJointAnnulusChartData hp hp1 m s W V c T r R z₀)
    {W₀ : Set (CoeffPair p)} (hs : SourcePsiIsolatingComplexExtension hp hp1 W₀ s)
    (n : ℤ) (hmn : m ≠ n) (φ : realTypeSourceLocus p)
    (hφ : φ.val ∈ V) (hφ₀ : φ.val ∈ W₀)
    (h : CoeffPair p) (hiso : SourceIsospectralDirection hp φ.val h) :
    let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val m
    sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet m φ.val *
        (fderiv ℂ (sourceAngularBeta hp hp1 n m s) φ.val) h =
      sourcePsiCandidate n (μ,(s n φ.val : Coeff p)) *
        (fderiv ℂ (fun ψ : CoeffPair p =>
          canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m) φ.val) h := by
  dsimp only
  let ρ := (r+R)/2
  have hrρ : r < ρ := by dsimp only [ρ]; linarith [D.inner_lt_outer]
  have hρR : ρ < R := by dsimp only [ρ]; linarith [D.inner_lt_outer]
  let μ : CoeffPair p → ℂ := fun ψ => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m
  let δ := sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet m
  let H := sourceAngularQuotientCauchyCandidate hp hp1 n m s (c m) r R z₀ ρ
  let P : ℂ × CoeffPair p → ℂ := fun t => 2*I*sourceStandardRootOmittedJointProduct hp hp1 m t
  let K : CoeffPair p → ℂ := fun ψ => P (μ ψ,ψ)
  let F : CoeffPair p → ℂ := fun ψ => H (μ ψ,ψ)
  let M : CoeffPair p → ℂ := fun ψ => sourceStandardRootMidpoint hp hp1 ψ m
  let G : CoeffPair p → ℂ := fun ψ =>
    (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)^2
  let q : CoeffPair p → ℂ := fun ψ => (μ ψ-M ψ)^2-G ψ/4
  have hμ : DifferentiableAt ℂ μ φ.val :=
    (analyticAt_canonicalPeriodOneBoundaryRoots_of_realType hp hp1 .dirichlet φ.val φ.property m).differentiableAt
  have hδ : DifferentiableAt ℂ δ φ.val :=
    (analyticAt_sourceBoundaryTerminalAntiDiscriminant_of_realType hp hp1 .dirichlet m φ.val φ.property).differentiableAt
  have hterminal : μ φ.val ∈ ball (c m) ρ :=
    ball_subset_ball hrρ.le (D.terminal_enclosed φ.val hφ)
  have hother (ψ : CoeffPair p) (hψ : ψ ∈ V) :
      μ ψ ∈ sourceStandardRootOmittedDomain hp hp1 ψ m :=
    ((D.disc_family ψ hψ).contour_family.2 m).2.2.1
      (ball_subset_closedBall ((D.disc_family ψ hψ).dirichlet_mem_ball m))
  have hKne : K φ.val ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) I_ne_zero)
      (sourceStandardRootOmittedProduct_ne_zero hp hp1 φ.val (μ φ.val) m (hother φ.val hφ))
  have hgraph : AnalyticAt ℂ (fun ψ : CoeffPair p => (μ ψ,ψ)) φ.val :=
    (analyticAt_canonicalPeriodOneBoundaryRoots_of_realType hp hp1 .dirichlet φ.val φ.property m).prod analyticAt_id
  have hK : DifferentiableAt ℂ K φ.val :=
    ((analyticAt_const.mul (D.omitted_analytic (μ φ.val,φ.val)
      ⟨(D.disc_family φ.val hφ).dirichlet_mem_ball m,hφ⟩)).comp
        (f := fun ψ : CoeffPair p => (μ ψ,ψ)) hgraph).differentiableAt
  obtain ⟨A,_,_,hAreal,hMG⟩ := exists_global_source_analytic_midpoint_squaredGap hp hp1
  have hM : DifferentiableAt ℂ M φ.val := (hMG φ.val (hAreal φ.property) m).1.differentiableAt
  have hG : DifferentiableAt ℂ G φ.val := (hMG φ.val (hAreal φ.property) m).2.differentiableAt
  have hMGzero : (fderiv ℂ M φ.val) h = 0 ∧ (fderiv ℂ G φ.val) h = 0 :=
    fderiv_canonicalPeriodicMidpoint_squaredGap_isospectral_eq_zero hp hp1 φ.val φ.property h hiso m
  have hq := ((hμ.hasFDerivAt.fun_sub hM.hasFDerivAt).pow 2).fun_sub
    (hG.hasFDerivAt.mul_const (4 : ℂ)⁻¹)
  change HasFDerivAt q _ φ.val at hq
  have hqvariation : (fderiv ℂ q φ.val) h =
      2*(μ φ.val-M φ.val)*(fderiv ℂ μ φ.val) h := by
    rw [hq.fderiv]
    simp only [sub_apply,smul_apply,smul_eq_mul,hMGzero.1,hMGzero.2,sub_zero,mul_zero]
    ring
  have hsquare (ψ : CoeffPair p) (hψ : ψ ∈ V) : δ ψ^2 = K ψ^2*q ψ := by
    dsimp only [δ,sourceBoundaryTerminalAntiDiscriminant,K,P,sourceStandardRootOmittedJointProduct,
      q,M,G,μ,sourceStandardRootMidpoint]
    rw [← sourceDiscriminant_sq_sub_four_at_canonicalDirichletRoot hp hp1 ψ m,
      canonicalDiscriminant_sq_sub_four_eq_midpoint_mul hp hp1 _ (periodOnePotential_mem ψ) m,
      ← sourceStandardRootOmittedProduct_sq_eq_canonicalDeletedPeriodicProduct hp hp1 ψ m _ (hother ψ hψ)]
    simp only [mul_pow,I_sq]
    ring
  have hnear : (fun ψ : CoeffPair p => δ ψ^2) =ᶠ[𝓝 φ.val] (fun ψ => K ψ^2*q ψ) := by
    filter_upwards [D.source_open.mem_nhds hφ] with ψ hψ
    exact hsquare ψ hψ
  have hsheet : δ φ.val*(fderiv ℂ δ φ.val) h =
      K φ.val*(fderiv ℂ K φ.val) h*q φ.val+
        K φ.val^2*(μ φ.val-M φ.val)*(fderiv ℂ μ φ.val) h := by
    have he := congrArg (fun L : CoeffPair p →L[ℂ] ℂ => L h) hnear.fderiv_eq
    have hd := (hδ.hasFDerivAt.pow 2).fderiv
    have hkq := ((hK.hasFDerivAt.pow 2).fun_mul hq).fderiv
    change fderiv ℂ (fun ψ : CoeffPair p => δ ψ^2) φ.val = _ at hd
    change fderiv ℂ (fun ψ : CoeffPair p => K ψ^2*q ψ) φ.val = _ at hkq
    rw [hd,hkq] at he
    simp only [add_apply,smul_apply,smul_eq_mul] at he
    rw [← hq.fderiv,hqvariation] at he
    linear_combination he/2
  have hbeta := D.fderiv_beta_isospectral_terminal_eq hs n hmn ρ hrρ hρR
    φ hφ hφ₀ h hiso
  change K φ.val^2*(fderiv ℂ (sourceAngularBeta hp hp1 n m s) φ.val) h =
      ((fderiv ℂ δ φ.val) h*K φ.val-δ φ.val*(fderiv ℂ K φ.val) h)*F φ.val+
        δ φ.val*K φ.val*deriv (fun z => H (z,φ.val)) (μ φ.val)*(fderiv ℂ μ φ.val) h at hbeta
  have heq := D.quotientCauchyCandidate_equation φ.val hφ n hmn ρ hrρ hρR (μ φ.val) hterminal
  have hresult := quadratic_sheet_terminal_variation (δ φ.val) (K φ.val) (q φ.val)
    (μ φ.val-M φ.val) (F φ.val) (deriv (fun z => H (z,φ.val)) (μ φ.val))
    (sourceAngularGapNumerator hp hp1 n m s φ.val (μ φ.val))
    ((fderiv ℂ μ φ.val) h) ((fderiv ℂ δ φ.val) h) ((fderiv ℂ K φ.val) h)
    ((fderiv ℂ (sourceAngularBeta hp hp1 n m s) φ.val) h) hKne (hsquare φ.val hφ) hsheet heq hbeta
  change δ φ.val*(fderiv ℂ (sourceAngularBeta hp hp1 n m s) φ.val) h = _
  rw [hresult]
  change K φ.val*(sourcePsiCandidate n (μ φ.val,(s n φ.val : Coeff p))/K φ.val)*
    (fderiv ℂ μ φ.val) h = _
  field_simp [hKne]
  rfl

/-- Every actual action gives the cleared beta/root bracket equation,
including periodic Dirichlet terminals and collapsed selected gaps. -/
theorem sourceBracket_beta_action_cleared
    (D : SourceAngularJointAnnulusChartData hp hp1 m s W V c T r R z₀)
    {W₀ : Set (CoeffPair p)} (hs : SourcePsiIsolatingComplexExtension hp hp1 W₀ s)
    (h2p : (2 : ℝ≥0∞) ≤ p) (n k : ℤ) (hmn : m ≠ n)
    (φ : realTypeSourceLocus p) (hφ : φ.val ∈ V) (hφ₀ : φ.val ∈ W₀) :
    let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val m
    sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet m φ.val *
        sourceBracket h2p (sourceAngularBeta hp hp1 n m s) (sourceComplexAction hp hp1 k) φ.val =
      sourcePsiCandidate n (μ,(s n φ.val : Coeff p)) *
        sourceBracket h2p (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m)
          (sourceComplexAction hp hp1 k) φ.val := by
  simpa only [fderiv_apply_sourceHamiltonianVector] using
    D.fderiv_beta_isospectral_cleared hs n hmn φ hφ hφ₀
      (sourceHamiltonianVector h2p (sourceComplexAction hp hp1 k) φ.val)
      (sourceHamiltonianVector_action_isospectral hp hp1 h2p φ.val φ.property k)

/-- At a regular terminal, the actual beta/action bracket is the actual
root/action bracket times the normalized differential on its sheet. -/
theorem sourceBracket_beta_action_eq_root_weight
    (D : SourceAngularJointAnnulusChartData hp hp1 m s W V c T r R z₀)
    {W₀ : Set (CoeffPair p)} (hs : SourcePsiIsolatingComplexExtension hp hp1 W₀ s)
    (h2p : (2 : ℝ≥0∞) ≤ p) (n k : ℤ) (hmn : m ≠ n)
    (φ : realTypeSourceLocus p) (hφ : φ.val ∈ V) (hφ₀ : φ.val ∈ W₀)
    (hδ : sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet m φ.val ≠ 0) :
    let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val m
    sourceBracket h2p (sourceAngularBeta hp hp1 n m s) (sourceComplexAction hp hp1 k) φ.val =
      sourcePsiCandidate n (μ,(s n φ.val : Coeff p)) /
        sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet m φ.val *
          sourceBracket h2p (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m)
            (sourceComplexAction hp hp1 k) φ.val := by
  dsimp only
  apply mul_left_cancel₀ hδ
  rw [D.sourceBracket_beta_action_cleared hs h2p n k hmn φ hφ hφ₀]
  field_simp [hδ]

end SourceAngularJointAnnulusChartData
end NLS.ZakharovShabat
