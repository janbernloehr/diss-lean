import NLS.ComplexAnalysis.QuadraticSheetTerminalVariation
import NLS.ZakharovShabat.SourceAngularEtaCauchyIsospectral
import NLS.ZakharovShabat.SourceAngularEtaCauchyTerminal
import NLS.ZakharovShabat.SourceBoundaryTerminalDifferential

/-! # The actual moving eta remainder in isospectral directions

Differentiating its actual Cauchy terminal formula gives the diagonal
normalized numerator minus the model numerator. The cleared variation
includes periodic terminals and collapsed gaps, and will combine with
the actual model-angle variation to give the full eta differential.
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

/-- The actual diagonal remainder variation, with no division by the
terminal square root. Its model term is retained with the exact sign. -/
theorem fderiv_etaRemainder_isospectral_cleared
    (D : SourceAngularJointAnnulusChartData hp hp1 m s W V c T r R z₀)
    {W₀ : Set (CoeffPair p)} (hs : SourcePsiIsolatingComplexExtension hp hp1 W₀ s)
    (ρ : ℝ) (hrρ : r < ρ) (hρR : ρ < R)
    (φ : realTypeSourceLocus p) (hφ : φ.val ∈ V) (hφ₀ : φ.val ∈ W₀)
    (h : CoeffPair p) (hiso : SourceIsospectralDirection hp φ.val h) :
    let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val m
    sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet m φ.val *
        (fderiv ℂ (sourceAngularEtaRemainderCauchyCandidate hp hp1 m s (c m) r R z₀ ρ) φ.val) h =
      (sourcePsiCandidate m (μ,(s m φ.val : Coeff p))-
        I*(2*I*sourceStandardRootOmittedProduct hp hp1 m φ.val μ)) *
          (fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m) φ.val) h := by
  dsimp only
  let μ : CoeffPair p → ℂ := fun ψ => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m
  let δ := sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet m
  let H := sourceAngularEtaQuotientCauchyCandidate hp hp1 m s (c m) r R z₀ ρ
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
  have hHjoint : DifferentiableAt ℂ H (μ φ.val,φ.val) :=
    (D.analyticOnNhd_etaQuotientCauchyCandidate ρ hrρ hρR _ ⟨hterminal,hφ⟩).differentiableAt
  have hF : DifferentiableAt ℂ F φ.val :=
    hHjoint.comp φ.val (f := fun ψ : CoeffPair p => (μ ψ,ψ)) hgraph.differentiableAt
  have hFvariation : (fderiv ℂ F φ.val) h =
      deriv (fun z => H (z,φ.val)) (μ φ.val)*(fderiv ℂ μ φ.val) h := by
    rw [fderiv_moving_spectral_parameter H μ φ.val hHjoint hμ]
    simp only [add_apply,smul_apply,smul_eq_mul]
    rw [D.fderiv_etaQuotientCauchyCandidate_isospectral_eq_zero hs ρ hrρ hρR
      φ hφ hφ₀ h hiso (μ φ.val) hterminal,zero_add]
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
  let B : CoeffPair p → ℂ := fun ψ => δ ψ*(K ψ)⁻¹*F ψ
  have hBnear : B =ᶠ[𝓝 φ.val] sourceAngularEtaRemainderCauchyCandidate hp hp1 m s (c m) r R z₀ ρ :=
    Filter.Eventually.of_forall (fun _ => rfl)
  have hi := (hasFDerivAt_inv hKne).comp φ.val hK.hasFDerivAt
  have hB := (hδ.hasFDerivAt.fun_mul hi).fun_mul hF.hasFDerivAt
  simp only [Function.comp_def] at hB
  have hbeta : K φ.val^2*(fderiv ℂ (sourceAngularEtaRemainderCauchyCandidate hp hp1 m s (c m) r R z₀ ρ) φ.val) h =
      ((fderiv ℂ δ φ.val) h*K φ.val-δ φ.val*(fderiv ℂ K φ.val) h)*F φ.val+
        δ φ.val*K φ.val*deriv (fun z => H (z,φ.val)) (μ φ.val)*(fderiv ℂ μ φ.val) h := by
    rw [← hBnear.fderiv_eq,hB.fderiv]
    simp only [add_apply,smul_apply,smul_eq_mul,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply]
    rw [hFvariation]
    field_simp [hKne]
    ring
  have heq := D.etaQuotientCauchyCandidate_equation φ.val hφ ρ hrρ hρR (μ φ.val) hterminal
  have hresult := quadratic_sheet_terminal_variation (δ φ.val) (K φ.val) (q φ.val)
    (μ φ.val-M φ.val) (F φ.val) (deriv (fun z => H (z,φ.val)) (μ φ.val))
    (sourceAngularGapNumerator hp hp1 m m s φ.val (μ φ.val)-I)
    ((fderiv ℂ μ φ.val) h) ((fderiv ℂ δ φ.val) h) ((fderiv ℂ K φ.val) h)
    ((fderiv ℂ (sourceAngularEtaRemainderCauchyCandidate hp hp1 m s (c m) r R z₀ ρ) φ.val) h) hKne (hsquare φ.val hφ) hsheet heq hbeta
  change δ φ.val*(fderiv ℂ (sourceAngularEtaRemainderCauchyCandidate
    hp hp1 m s (c m) r R z₀ ρ) φ.val) h =
      (sourcePsiCandidate m (μ φ.val,(s m φ.val : Coeff p))-I*K φ.val)*(fderiv ℂ μ φ.val) h
  rw [hresult]
  change K φ.val*(sourcePsiCandidate m (μ φ.val,(s m φ.val : Coeff p))/K φ.val-I)*
    (fderiv ℂ μ φ.val) h = _
  field_simp [hKne]

/-- Every actual action gives the cleared variation of the actual
eta remainder, including the collapsed selected gap. -/
theorem sourceBracket_etaRemainder_action_cleared
    (D : SourceAngularJointAnnulusChartData hp hp1 m s W V c T r R z₀)
    {W₀ : Set (CoeffPair p)} (hs : SourcePsiIsolatingComplexExtension hp hp1 W₀ s)
    (h2p : (2 : ℝ≥0∞) ≤ p) (k : ℤ) (ρ : ℝ) (hrρ : r < ρ) (hρR : ρ < R)
    (φ : realTypeSourceLocus p) (hφ : φ.val ∈ V) (hφ₀ : φ.val ∈ W₀) :
    let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val m
    sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet m φ.val *
        sourceBracket h2p (sourceAngularEtaRemainderCauchyCandidate hp hp1 m s (c m) r R z₀ ρ)
          (sourceComplexAction hp hp1 k) φ.val =
      (sourcePsiCandidate m (μ,(s m φ.val : Coeff p))-
        I*(2*I*sourceStandardRootOmittedProduct hp hp1 m φ.val μ)) *
          sourceBracket h2p (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m)
            (sourceComplexAction hp hp1 k) φ.val := by
  simpa only [fderiv_apply_sourceHamiltonianVector] using
    D.fderiv_etaRemainder_isospectral_cleared hs ρ hrρ hρR φ hφ hφ₀
      (sourceHamiltonianVector h2p (sourceComplexAction hp hp1 k) φ.val)
      (sourceHamiltonianVector_action_isospectral hp hp1 h2p φ.val φ.property k)

end SourceAngularJointAnnulusChartData
end NLS.ZakharovShabat
