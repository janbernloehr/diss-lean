import NLS.ZakharovShabat.SourceAngularBranchCosineLift
import NLS.ComplexAnalysis.CurveIntegralInteriorCongruence

/-! # Analytic eta representatives on complex half-gap charts

The endpoint-normalized primitive is jointly analytic and evaluates
the literal pulled-back diagonal differential on integrable angle paths.
An analytic actual terminal angle gives an analytic source value without
any real-source assumption, including either periodic endpoint.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def sourceAngularBranchEtaRepresentative (hp : p ≠ ⊤) (hp1 : 1 < p) (m : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (δ : CoeffPair p → ℂ) :
    ℂ × CoeffPair p → ℂ := fun x =>
  (-Complex.I) * sourceAngularBranchCosinePrimitive hp hp1 m m s δ x

@[simp] theorem sourceAngularBranchEtaRepresentative_pi
    (hp : p ≠ ⊤) (hp1 : 1 < p) (m : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (δ : CoeffPair p → ℂ) (ψ : CoeffPair p) :
    sourceAngularBranchEtaRepresentative hp hp1 m s δ ((Real.pi : ℂ),ψ) = 0 := by
  simp only [sourceAngularBranchEtaRepresentative,sourceAngularBranchCosinePrimitive_pi,mul_zero]

namespace SourceAngularBranchCosineChartData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {m : ℤ}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k} {δ : CoeffPair p → ℂ}
  {W V : Set (CoeffPair p)} {Ω : Set ℂ} {c : ℤ → ℂ} {R : ℤ → ℝ}

theorem analyticOnNhd_etaRepresentative
    (D : SourceAngularBranchCosineChartData hp hp1 m s δ W V Ω c R) :
    AnalyticOnNhd ℂ (sourceAngularBranchEtaRepresentative hp hp1 m s δ) (Ω ×ˢ V) :=
  fun x hx => analyticAt_const.mul (D.primitive_analytic m x hx)

/-- Endpoint singularities of the literal pullback are removable for
integration. No integrability hypotheses need to be supplied. -/
theorem etaRepresentative_eq_lifted_pathIntegral
    (D : SourceAngularBranchCosineChartData hp hp1 m s δ W V Ω c R)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (e : ℂ)
    (γ : Path (Real.pi : ℂ) e) (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hγΩ : ∀ t : unitInterval, γ t ∈ Ω)
    (hsin : ∀ t ∈ Ioo (0 : ℝ) 1, Complex.sin (γ.extend t) ≠ 0) :
    CurveIntegrable (holomorphicOneForm (fun θ =>
      sourceAngularBranchCosineLiftedIntegrand hp hp1 m m s δ (θ,ψ))) γ ∧
      (∫ᶜ θ in γ, holomorphicOneForm (fun θ =>
        sourceAngularBranchCosineLiftedIntegrand hp hp1 m m s δ (θ,ψ)) θ) =
          sourceAngularBranchEtaRepresentative hp hp1 m s δ (e,ψ) := by
  let f : ℂ → ℂ := fun θ => sourceAngularBranchCosineLiftedIntegrand hp hp1 m m s δ (θ,ψ)
  let g : ℂ → ℂ := fun θ => (-Complex.I) * sourceAngularGapNumerator hp hp1 m m s ψ
    (sourceAngularBranchCosinePoint hp hp1 m δ (θ,ψ))
  let F : ℂ → ℂ := fun θ => sourceAngularBranchEtaRepresentative hp hp1 m s δ (θ,ψ)
  have hg : AnalyticOnNhd ℂ g Ω := fun θ hθ =>
    analyticAt_const.mul ((D.numerator_analytic m (θ,ψ) ⟨hθ,hψ⟩).comp
      (f := fun θ : ℂ => (θ,ψ)) (analyticAt_id.prod analyticAt_const))
  have hγs : ∀ t ∈ Icc (0 : ℝ) 1, γ.extend t ∈ Ω := by
    intro t ht
    simpa only [Path.extend_apply γ ht] using hγΩ ⟨t,ht⟩
  have hint : CurveIntegrable (holomorphicOneForm g) γ :=
    (hg.continuousOn.smul continuousOn_const).curveIntegrable_of_contDiffOn hγ hγΩ
  have heq : ∀ t ∈ Ioo (0 : ℝ) 1, f (γ.extend t) = g (γ.extend t) :=
    fun t ht => D.cosineLiftedIntegrand_eq_gapNumerator ψ hψ m (γ.extend t)
      (hγs t (Ioo_subset_Icc_self ht)) (hsin t ht)
  have hF : ∀ θ ∈ Ω, HasDerivAt F (g θ) θ := fun θ hθ =>
    (D.primitive_derivative m ψ hψ θ hθ).const_mul (-Complex.I)
  refine ⟨(curveIntegrable_holomorphicOneForm_congr_interior f g γ heq).mpr hint,?_⟩
  change (∫ᶜ θ in γ, holomorphicOneForm f θ) = F e
  rw [curveIntegral_holomorphicOneForm_congr_interior f g γ heq,
    curveIntegral_eq_sub_of_primitive g F Ω hF γ hγ hγs hint]
  simp only [F,sourceAngularBranchEtaRepresentative_pi,sub_zero]

/-- A prescribed base terminal angle in the chart constructs an analytic
eta source value with the exact actual Dirichlet root normalization. -/
theorem exists_local_analytic_eta_at_terminal_angle
    (D : SourceAngularBranchCosineChartData hp hp1 m s δ W V Ω c R)
    (φ : CoeffPair p) (hφ : φ ∈ V)
    (hμ : AnalyticAt ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m) φ)
    (e : ℂ) (he : e ∈ Ω)
    (hpoint : sourceAngularBranchCosinePoint hp hp1 m δ (e,φ) = canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ m)
    (hsin : Complex.sin e = sourceAngularBranchDirichletSine hp hp1 m δ φ) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧ U ⊆ V ∧ ∃ ε : CoeffPair p → ℂ,
      AnalyticOnNhd ℂ ε U ∧ ε φ = e ∧
      (∀ ψ ∈ U, ε ψ ∈ Ω ∧
        sourceAngularBranchCosinePoint hp hp1 m δ (ε ψ,ψ) = canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m ∧
        Complex.sin (ε ψ) = sourceAngularBranchDirichletSine hp hp1 m δ ψ ∧
        sourceAngularBranchCosineRoot hp hp1 m δ (ε ψ,ψ) =
          sourceAntiDiscriminantCandidate hp hp1 ψ (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m)) ∧
      AnalyticOnNhd ℂ (fun ψ => sourceAngularBranchEtaRepresentative hp hp1 m s δ (ε ψ,ψ)) U := by
  let τ : CoeffPair p → ℂ := fun ψ => canonicalPeriodicMidpoint hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) m
  let μ : CoeffPair p → ℂ := fun ψ => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m
  let sine := sourceAngularBranchDirichletSine hp hp1 m δ
  have hgraph : AnalyticAt ℂ (fun ψ => (μ ψ,ψ)) φ := hμ.prod analyticAt_id
  have hprod := (D.omitted_analytic (μ φ,φ) ⟨(D.disc_family φ hφ).dirichlet_mem_ball m,hφ⟩).comp
    (f := fun ψ : CoeffPair p => (μ ψ,ψ)) hgraph
  have hanti := (analyticOnNhd_sourceAntiDiscriminantCandidate_joint hp hp1
    (μ φ,φ) (mem_univ _)).comp (f := fun ψ : CoeffPair p => (μ ψ,ψ)) hgraph
  have hprodne := sourceStandardRootOmittedProduct_ne_zero hp hp1 φ (μ φ) m
    (((D.disc_family φ hφ).contour_family.2 m).2.2.1
      (ball_subset_closedBall ((D.disc_family φ hφ).dirichlet_mem_ball m)))
  have hsine : AnalyticAt ℂ sine φ := hanti.div ((analyticAt_const.mul (D.halfGap_analytic φ hφ)).mul hprod)
    (mul_ne_zero (mul_ne_zero (by norm_num) (D.halfGap_ne_zero φ hφ)) hprodne)
  have hcircle : ∀ᶠ ψ in 𝓝 φ, sine ψ ^ 2 + ((μ ψ - τ ψ) / δ ψ) ^ 2 = 1 := by
    filter_upwards [D.source_open.mem_nhds hφ] with ψ hψ
    exact sourceAngularBranchDirichletSine_sq_add_cosine_sq hp hp1 m δ ψ
      (D.halfGap_ne_zero ψ hψ) (D.halfGap_sq ψ hψ)
      (((D.disc_family ψ hψ).contour_family.2 m).2.2.1
        (ball_subset_closedBall ((D.disc_family ψ hψ).dirichlet_mem_ball m)))
  obtain ⟨ε,hε,hεφ,hcoords⟩ := exists_analytic_parametricCosine_terminal_with_sine τ δ μ sine φ e
    (D.midpoint_analytic φ hφ) (D.halfGap_analytic φ hφ) hμ hsine
    (D.halfGap_ne_zero φ hφ) hsin.symm hpoint hcircle
  have hangle : ∀ᶠ ψ in 𝓝 φ, ε ψ ∈ Ω := hε.continuousAt.eventually
    (D.angle_open.mem_nhds (hεφ.symm ▸ he))
  have hgood : ∀ᶠ ψ in 𝓝 φ, ψ ∈ V ∧ AnalyticAt ℂ ε ψ ∧ ε ψ ∈ Ω ∧
      sourceAngularBranchCosinePoint hp hp1 m δ (ε ψ,ψ) = μ ψ ∧ Complex.sin (ε ψ) = sine ψ := by
    filter_upwards [D.source_open.mem_nhds hφ,hε.eventually_analyticAt,hangle,hcoords] with ψ hv ha he hc
    exact ⟨hv,ha,he,hc⟩
  obtain ⟨U,hUsub,hU,hφU⟩ := _root_.mem_nhds_iff.mp hgood
  refine ⟨U,hU,hφU,(fun ψ hψ => (hUsub hψ).1),ε,(fun ψ hψ => (hUsub hψ).2.1),hεφ,?_,?_⟩
  · intro ψ hψ
    obtain ⟨hv,_,he,hpnt,hs⟩ := hUsub hψ
    exact ⟨he,hpnt,hs,sourceAngularBranchCosineRoot_eq_dirichlet_anti hp hp1 m δ ψ (ε ψ)
      (D.halfGap_ne_zero ψ hv)
      (((D.disc_family ψ hv).contour_family.2 m).2.2.1
        (ball_subset_closedBall ((D.disc_family ψ hv).dirichlet_mem_ball m))) hpnt hs⟩
  · intro ψ hψ
    exact (D.analyticOnNhd_etaRepresentative (ε ψ,ψ) ⟨(hUsub hψ).2.2.1,(hUsub hψ).1⟩).comp
      (f := fun ψ : CoeffPair p => (ε ψ,ψ)) (((hUsub hψ).2.1).prod analyticAt_id)

end SourceAngularBranchCosineChartData
end NLS.ZakharovShabat
