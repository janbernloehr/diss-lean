import NLS.ZakharovShabat.SourceAngularBetaCauchyAnalytic
import NLS.ZakharovShabat.SourceAngularEtaDifferential
import NLS.ZakharovShabat.SourceBoundaryTerminalDifferential

/-! # Actual terminal Cauchy cotangents at periodic endpoints

The actual beta and eta remainder contain the full moving terminal
anti-discriminant as a factor. When that factor vanishes, the product
rule removes all other source and terminal derivative terms. Their full
cotangents become scalar multiples of the moving anti-discriminant
cotangent, including collapsed beta gaps. No isospectral-direction
premise or division by the vanishing terminal is used.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceAngularJointAnnulusChartData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {m : ℤ}
  {s : (j : ℤ) → CoeffPair p → DeletedCoeff p j}
  {W V : Set (CoeffPair p)} {c : ℤ → ℂ} {T : ℤ → ℝ} {r R : ℝ} {z₀ : ℂ}

/-- The full derivative of any actual analytic terminal Cauchy quotient
at a periodic terminal retains only the moving anti-discriminant factor. -/
theorem fderiv_terminalCauchy_of_anti_eq_zero
    (D : SourceAngularJointAnnulusChartData hp hp1 m s W V c T r R z₀)
    (φ : realTypeSourceLocus p) (hφ : φ.val ∈ V) (H : ℂ × CoeffPair p → ℂ)
    (hH : AnalyticAt ℂ H (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val m,φ.val))
    (hzero : sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet m φ.val = 0) :
    fderiv ℂ (fun ψ : CoeffPair p =>
      let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m
      sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet m ψ /
        (2*I*sourceStandardRootOmittedProduct hp hp1 m ψ μ)*H (μ,ψ)) φ.val =
      (H (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val m,φ.val) /
        (2*I*sourceStandardRootOmittedProduct hp hp1 m φ.val
          (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val m))) •
        fderiv ℂ (sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet m) φ.val := by
  let μ : CoeffPair p → ℂ := fun ψ => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m
  let S := sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet m
  let K : CoeffPair p → ℂ := fun ψ => 2*I*sourceStandardRootOmittedProduct hp hp1 m ψ (μ ψ)
  let G : CoeffPair p → ℂ := fun ψ => H (μ ψ,ψ)/K ψ
  have hgraph : AnalyticAt ℂ (fun ψ => (μ ψ,ψ)) φ.val :=
    (analyticAt_canonicalPeriodOneBoundaryRoots_of_realType hp hp1 .dirichlet φ.val φ.property m).prod analyticAt_id
  have hK : AnalyticAt ℂ K φ.val := analyticAt_const.mul
    ((D.omitted_analytic (μ φ.val,φ.val) ⟨(D.disc_family φ.val hφ).dirichlet_mem_ball m,hφ⟩).comp
      (f := fun ψ : CoeffPair p => (μ ψ,ψ)) hgraph)
  have hKne : K φ.val ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) I_ne_zero)
      (sourceStandardRootOmittedProduct_ne_zero hp hp1 φ.val (μ φ.val) m
        (((D.disc_family φ.val hφ).contour_family.2 m).2.2.1
          (ball_subset_closedBall ((D.disc_family φ.val hφ).dirichlet_mem_ball m))))
  have hG : DifferentiableAt ℂ G φ.val :=
    ((hH.comp (f := fun ψ : CoeffPair p => (μ ψ,ψ)) hgraph).div hK hKne).differentiableAt
  have hS := (analyticAt_sourceBoundaryTerminalAntiDiscriminant_of_realType hp hp1 .dirichlet m φ.val φ.property).differentiableAt
  have heq : (fun ψ : CoeffPair p => S ψ/K ψ*H (μ ψ,ψ)) = (fun ψ => S ψ*G ψ) := by
    funext ψ
    dsimp only [G]
    ring
  change fderiv ℂ (fun ψ : CoeffPair p => S ψ/K ψ*H (μ ψ,ψ)) φ.val = G φ.val • fderiv ℂ S φ.val
  rw [heq,fderiv_fun_mul hS hG,hzero]
  apply ContinuousLinearMap.ext
  intro h
  simp [S]

/-- The actual off-diagonal beta cotangent at either periodic terminal
is a scalar multiple of the full moving terminal anti-discriminant cotangent. -/
theorem fderiv_beta_eq_anti_smul_of_eq_zero
    (D : SourceAngularJointAnnulusChartData hp hp1 m s W V c T r R z₀)
    (n : ℤ) (hmn : m ≠ n) (ρ : ℝ) (hrρ : r < ρ) (hρR : ρ < R)
    (φ : realTypeSourceLocus p) (hφ : φ.val ∈ V)
    (hzero : sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet m φ.val = 0) :
    fderiv ℂ (sourceAngularBeta hp hp1 n m s) φ.val =
      (sourceAngularQuotientCauchyCandidate hp hp1 n m s (c m) r R z₀ ρ
        (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val m,φ.val) /
        (2*I*sourceStandardRootOmittedProduct hp hp1 m φ.val
          (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val m))) •
        fderiv ℂ (sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet m) φ.val := by
  have heq : sourceAngularBetaCauchyCandidate hp hp1 n m s (c m) r R z₀ ρ =ᶠ[𝓝 φ.val]
      sourceAngularBeta hp hp1 n m s := by
    filter_upwards [D.source_open.mem_nhds hφ] with ψ hψ
    exact D.betaCauchyCandidate_eq_beta ψ hψ n hmn ρ hrρ hρR
  rw [← heq.fderiv_eq]
  exact D.fderiv_terminalCauchy_of_anti_eq_zero φ hφ _
    (D.analyticOnNhd_quotientCauchyCandidate n ρ hrρ hρR _
      ⟨ball_subset_ball hrρ.le (D.terminal_enclosed φ.val hφ),hφ⟩) hzero

/-- The actual eta remainder has the same full endpoint cotangent
reduction, with its own constructed analytic Cauchy quotient. -/
theorem fderiv_etaRemainder_eq_anti_smul_of_eq_zero
    (D : SourceAngularJointAnnulusChartData hp hp1 m s W V c T r R z₀)
    (ρ : ℝ) (hrρ : r < ρ) (hρR : ρ < R)
    (φ : realTypeSourceLocus p) (hφ : φ.val ∈ V)
    (hzero : sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet m φ.val = 0) :
    fderiv ℂ (sourceAngularEtaRemainderCauchyCandidate hp hp1 m s (c m) r R z₀ ρ) φ.val =
      (sourceAngularEtaQuotientCauchyCandidate hp hp1 m s (c m) r R z₀ ρ
        (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val m,φ.val) /
        (2*I*sourceStandardRootOmittedProduct hp hp1 m φ.val
          (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val m))) •
        fderiv ℂ (sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet m) φ.val :=
  D.fderiv_terminalCauchy_of_anti_eq_zero φ hφ _
    (D.analyticOnNhd_etaQuotientCauchyCandidate ρ hrρ hρR _
      ⟨ball_subset_ball hrρ.le (D.terminal_enclosed φ.val hφ),hφ⟩) hzero

end SourceAngularJointAnnulusChartData
end NLS.ZakharovShabat
