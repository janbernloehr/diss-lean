import NLS.ZakharovShabat.SourceAngularEndpointCauchyCotangent

/-! # The actual diagonal eta cotangent at periodic terminals

The constructed terminal angle satisfies the exact moving sine equation.
At a periodic terminal its sine is zero and its cosine is nonzero. The
full source derivative therefore reduces to the moving anti-discriminant
cotangent. Adding the endpoint Cauchy remainder gives the same reduction
for the actual single eta cotangent, without an isospectral hypothesis.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceAngularEtaAnalyticChartData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {m : ℤ}
  {s : (j : ℤ) → CoeffPair p → DeletedCoeff p j}
  {W V U : Set (CoeffPair p)} {c : ℤ → ℂ} {T : ℤ → ℝ}
  {r R ρ : ℝ} {z₀ : ℂ} {δ ε : CoeffPair p → ℂ}

/-- The actual terminal angle has a full endpoint cotangent formula;
its coefficient divides only nonzero half-gap, omitted product and cosine. -/
theorem fderiv_modelAngle_eq_anti_smul_of_eq_zero
    (D : SourceAngularEtaAnalyticChartData hp hp1 m s W V U c T r R z₀ ρ δ ε)
    (φ : realTypeSourceLocus p) (hφ : φ.val ∈ U)
    (hzero : sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet m φ.val = 0) :
    fderiv ℂ ε φ.val =
      (2*δ φ.val*sourceStandardRootOmittedProduct hp hp1 m φ.val
        (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val m)*Complex.cos (ε φ.val))⁻¹ •
        fderiv ℂ (sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet m) φ.val := by
  let μ : CoeffPair p → ℂ := fun ψ => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m
  let S := sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet m
  change S φ.val = 0 at hzero
  let A : CoeffPair p → ℂ := fun ψ => 2*δ ψ*sourceStandardRootOmittedProduct hp hp1 m ψ (μ ψ)
  have hφV := D.angle.source_subset hφ
  have hgraph : AnalyticAt ℂ (fun ψ : CoeffPair p => (μ ψ,ψ)) φ.val :=
    (analyticAt_canonicalPeriodOneBoundaryRoots_of_realType hp hp1 .dirichlet φ.val φ.property m).prod analyticAt_id
  have hP : AnalyticAt ℂ (fun ψ : CoeffPair p => sourceStandardRootOmittedProduct hp hp1 m ψ (μ ψ)) φ.val :=
    (D.annulus.omitted_analytic (μ φ.val,φ.val)
      ⟨(D.annulus.disc_family φ.val hφV).dirichlet_mem_ball m,hφV⟩).comp
      (f := fun ψ : CoeffPair p => (μ ψ,ψ)) hgraph
  have hA : DifferentiableAt ℂ A φ.val :=
    ((analyticAt_const.mul (D.angle.halfGap_analytic φ.val hφ)).mul hP).differentiableAt
  have hAne : A φ.val ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (D.angle.halfGap_ne_zero φ.val hφ))
      (sourceStandardRootOmittedProduct_ne_zero hp hp1 φ.val (μ φ.val) m
        (((D.annulus.disc_family φ.val hφV).contour_family.2 m).2.2.1
          (ball_subset_closedBall ((D.annulus.disc_family φ.val hφV).dirichlet_mem_ball m))))
  have hε : DifferentiableAt ℂ ε φ.val := (D.angle.angle_analytic φ.val hφ).differentiableAt
  have hnear : (fun ψ : CoeffPair p => A ψ*Complex.sin (ε ψ)) =ᶠ[𝓝 φ.val] S := by
    filter_upwards [D.angle.source_open.mem_nhds hφ] with ψ hψ
    have ht := D.angle.terminal_root ψ hψ
    simpa only [sourceAngularBranchCosineRoot,(D.angle.terminal_coordinates ψ hψ).1,
      A,S,μ,sourceBoundaryTerminalAntiDiscriminant] using ht
  have hsin : Complex.sin (ε φ.val) = 0 := by
    have ht := hnear.eq_of_nhds
    rw [hzero] at ht
    exact (mul_eq_zero.mp ht).resolve_left hAne
  have hcos : Complex.cos (ε φ.val) ≠ 0 := by
    intro hc
    have ht := Complex.sin_sq_add_cos_sq (ε φ.val)
    rw [hsin,hc] at ht
    norm_num at ht
  have hd := hnear.fderiv_eq.symm.trans (hA.hasFDerivAt.fun_mul hε.hasFDerivAt.csin).fderiv
  have hd' : fderiv ℂ S φ.val = (A φ.val*Complex.cos (ε φ.val)) • fderiv ℂ ε φ.val := by
    apply ContinuousLinearMap.ext
    intro h
    have he := congrArg (fun L : CoeffPair p →L[ℂ] ℂ => L h) hd
    simpa [hsin,smul_smul,smul_eq_mul] using he
  change fderiv ℂ ε φ.val = (A φ.val*Complex.cos (ε φ.val))⁻¹ • fderiv ℂ S φ.val
  rw [hd']
  apply ContinuousLinearMap.ext
  intro h
  simp only [smul_apply,smul_eq_mul,← mul_assoc,inv_mul_cancel₀ (mul_ne_zero hAne hcos),one_mul]

/-- The actual single eta cotangent at either periodic endpoint lies
in the span of its full moving terminal anti-discriminant cotangent. -/
theorem exists_etaDifferential_eq_anti_smul_of_eq_zero
    (D : SourceAngularEtaAnalyticChartData hp hp1 m s W V U c T r R z₀ ρ δ ε)
    (φ : realTypeSourceLocus p) (hφ : φ.val ∈ U)
    (hzero : sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet m φ.val = 0) :
    ∃ a : ℂ, sourceAngularEtaDifferential hp hp1 m s φ.val =
      a • fderiv ℂ (sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet m) φ.val := by
  rw [D.etaDifferential_eq_fderiv_representative φ.val hφ]
  have hε := (D.angle.angle_analytic φ.val hφ).differentiableAt
  have hμ := analyticAt_canonicalPeriodOneBoundaryRoots_of_realType hp hp1 .dirichlet φ.val φ.property m
  have hR := (D.annulus.analyticAt_etaRemainderCauchyCandidate ρ D.inner_lt_cauchy D.cauchy_lt_outer
    φ.val (D.angle.source_subset hφ) hμ).differentiableAt
  have hd := ((hε.hasFDerivAt.sub_const (Real.pi:ℂ)).fun_add hR.hasFDerivAt).fderiv
  change fderiv ℂ (sourceAngularEtaCauchyRepresentative hp hp1 m s (c m) r R z₀ ρ ε) φ.val = _ at hd
  rw [hd,D.fderiv_modelAngle_eq_anti_smul_of_eq_zero φ hφ hzero,
    D.annulus.fderiv_etaRemainder_eq_anti_smul_of_eq_zero ρ D.inner_lt_cauchy D.cauchy_lt_outer
      φ (D.angle.source_subset hφ) hzero,← add_smul]
  exact ⟨_,rfl⟩

end SourceAngularEtaAnalyticChartData
end NLS.ZakharovShabat
