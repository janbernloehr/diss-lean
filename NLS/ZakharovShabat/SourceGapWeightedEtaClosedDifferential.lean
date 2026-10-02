import NLS.ZakharovShabat.SourceBirkhoffFixedFamilyAnalytic
import NLS.ZakharovShabat.SourceBoundaryTerminalDifferential

/-! # Gap-weighted eta derivatives at real collapsed gaps

The analytic formula has zero amplitude and zero normalized remainder
at a collapsed real gap. Differentiating it leaves the actual midpoint,
Dirichlet-root, and moving anti-discriminant cotangents. No division by
the gap or definition of an angle at a closed gap is required.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceAngularJointAnnulusChartData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {n : ℤ}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}
  {W V : Set (CoeffPair p)} {c : ℤ → ℂ} {T : ℤ → ℝ} {r R : ℝ} {z₀ : ℂ}

/-- The full derivative formula at a real collapsed gap. The last term
is the derivative of the moving terminal anti-discriminant. -/
theorem fderiv_gapWeightedEtaCoordinate_of_real_closed_gap
    (D : SourceAngularJointAnnulusChartData hp hp1 n s W V c T r R z₀)
    (ρ : ℝ) (hrρ : r < ρ) (hρR : ρ < R)
    (hμ : AnalyticOnNhd ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n) V)
    (φ : CoeffPair p) (hφ : φ ∈ V) (hreal : IsRealType (CoeffPair.toMax p φ))
    (hτ : AnalyticAt ℂ (fun ψ : CoeffPair p => canonicalPeriodicMidpoint hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) n) φ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n = 0)
    (sign : ℂ) :
    fderiv ℂ (sourceGapWeightedEtaCoordinate hp hp1 n s sign) φ =
      (-2 : ℂ) • (fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n) φ -
        fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodicMidpoint hp hp1
          (periodOnePotential ψ) (periodOnePotential_mem ψ) n) φ +
        (sign*I/(2*sourceStandardRootOmittedProduct hp hp1 n φ
          (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ n))) •
          fderiv ℂ (sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet n) φ) := by
  let μ := fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n
  let τ := fun ψ : CoeffPair p => canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  let P := fun ψ : CoeffPair p => sourceStandardRootOmittedProduct hp hp1 n ψ (μ ψ)
  let S := sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet n
  let B := sourceDirichletEtaSineNumerator hp hp1 n
  have hμball := (D.disc_family φ hφ).dirichlet_mem_ball n
  have hPne : P φ ≠ 0 := sourceStandardRootOmittedProduct_ne_zero hp hp1 φ (μ φ) n
    (((D.disc_family φ hφ).contour_family.2 n).2.2.1 (ball_subset_closedBall hμball))
  have hPa : AnalyticAt ℂ P φ := (D.omitted_analytic (μ φ,φ) ⟨hμball,hφ⟩).comp
    (f := fun ψ : CoeffPair p => (μ ψ,ψ)) ((hμ φ hφ).prod analyticAt_id)
  have hSa := analyticAt_sourceBoundaryTerminalAntiDiscriminant_of_realType hp hp1 .dirichlet n φ hreal
  have hS0 : S φ = 0 := sourceAntiDiscriminant_at_canonicalBoundaryRoot_eq_zero_of_collapsed_gap hp hp1 .dirichlet φ hreal n hgap
  have hB0 : B φ = 0 := by change S φ / (2*P φ) = 0; rw [hS0,zero_div]
  have hBdiff := (D.analyticOnNhd_dirichletEtaSineNumerator hμ φ hφ).differentiableAt
  have hBi : fderiv ℂ B φ = (2*P φ)⁻¹ • fderiv ℂ S φ := by
    have hi := ((hPa.differentiableAt.const_mul 2).inv (mul_ne_zero (by norm_num) hPne)).hasFDerivAt
    have hd := (hSa.differentiableAt.hasFDerivAt.fun_mul hi).fderiv
    change fderiv ℂ (fun ψ => S ψ / (2*P ψ)) φ = _
    change fderiv ℂ (fun ψ => S ψ * (2*P ψ)⁻¹) φ = S φ • _ + (2*P φ)⁻¹ • fderiv ℂ S φ at hd
    ext h
    have he := congrArg (fun L : CoeffPair p →L[ℂ] ℂ => L h) hd
    simpa only [div_eq_mul_inv,add_apply,smul_apply,
      smul_eq_mul,hS0,zero_mul,zero_add] using he
  have hμτ : μ φ = τ φ := sourceDirichletRoot_eq_midpoint_of_real_collapsed_gap hp hp1 φ hreal n
    (by simpa only [sourcePeriodicGapDisplacement_apply] using hgap)
  have hend : SourceAngularDirichletTerminalIsEndpoint hp hp1 φ n :=
    Or.inl (canonicalPeriodOneBoundaryRoots_eq_of_collapsed_gap hp hp1 .dirichlet φ hreal n (sub_eq_zero.mp hgap).symm)
  have hH0 := D.etaRemainder_eq_zero_of_endpoint ρ hrρ hρR φ hφ hend
  have hA := ((hμ φ hφ).differentiableAt.hasFDerivAt.sub hτ.differentiableAt.hasFDerivAt).add
    (hBdiff.hasFDerivAt.const_mul (sign*I))
  have hE : AnalyticAt ℂ (fun ψ => Complex.exp (sign*I*sourceAngularEtaRemainder hp hp1 n s ψ)) φ := (analyticAt_const.mul (D.analyticOnNhd_etaRemainder ρ hrρ hρR hμ φ hφ)).cexp'
  have hd := ((hA.const_mul (-2)).fun_mul hE.differentiableAt.hasFDerivAt).fderiv
  change fderiv ℂ (sourceGapWeightedEtaCoordinate hp hp1 n s sign) φ = _ at hd
  rw [hd]
  change _ = (-2 : ℂ) • (fderiv ℂ μ φ - fderiv ℂ τ φ + (sign*I/(2*P φ)) • fderiv ℂ S φ)
  dsimp only [Pi.add_apply,Pi.sub_apply]
  dsimp only [μ,τ] at hμτ
  dsimp only [B] at hB0 hBi
  rw [hH0,hμτ,hB0,hBi]
  ext h
  simp only [add_apply,smul_apply,
    sub_apply,smul_eq_mul,mul_zero,Complex.exp_zero,sub_self,add_zero,one_mul,div_eq_mul_inv]
  ring

end SourceAngularJointAnnulusChartData
end NLS.ZakharovShabat
