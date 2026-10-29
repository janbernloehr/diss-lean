import NLS.ComplexAnalysis.AnalyticImplicitBanachRoot
import NLS.ZakharovShabat.SourceBoundarySimpleNeighborhood
import NLS.ZakharovShabat.SourceLemma9_2

/-! Local analytic simple-root branches used in Section 9. The branch is
constructed at an arbitrary complex source; no continuous root selection
or global continuity of the lexicographic labels is assumed. -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Any simple ordinary characteristic zero has a locally analytic branch
of simple zeros in the original complex source space. -/
theorem exists_local_analytic_sourceBoundary_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition)
    (φ : CoeffPair p) (z : ℂ)
    (hz : periodOneBoundaryCharacteristic hp hp1 b φ z = 0)
    (hs : deriv (periodOneBoundaryCharacteristic hp hp1 b φ) z ≠ 0) :
    ∃ μ : CoeffPair p → ℂ, ∃ U : Set (CoeffPair p),
      IsOpen U ∧ φ ∈ U ∧ μ φ = z ∧ AnalyticOnNhd ℂ μ U ∧
      ∀ ψ ∈ U, periodOneBoundaryCharacteristic hp hp1 b ψ (μ ψ) = 0 ∧
        deriv (periodOneBoundaryCharacteristic hp hp1 b ψ) (μ ψ) ≠ 0 := by
  let F : ℂ × CoeffPair p → ℂ := fun t => periodOneBoundaryCharacteristic hp hp1 b t.2 t.1
  have hF : AnalyticAt ℂ F (z,φ) :=
    analyticOnNhd_periodOneBoundaryCharacteristic_joint hp hp1 b (z,φ) (mem_univ _)
  have hd := (analyticOnNhd_periodOneBoundaryCharacteristic hp hp1 b φ z
    (mem_univ _)).differentiableAt.hasDerivAt
  have hpartial : (fderiv ℂ F (z,φ)).comp (ContinuousLinearMap.inl ℂ ℂ (CoeffPair p)) =
      ContinuousLinearMap.toSpanSingleton ℂ (deriv (periodOneBoundaryCharacteristic hp hp1 b φ) z) := by
    have hc : HasFDerivAt (fun w => F (w,φ))
        ((fderiv ℂ F (z,φ)).comp (ContinuousLinearMap.inl ℂ ℂ (CoeffPair p))) z :=
      hF.differentiableAt.hasFDerivAt.comp (f := fun w : ℂ => (w,φ)) z
        (hasFDerivAt_prodMk_left z φ)
    exact hc.unique hd.hasFDerivAt
  have hbij : Function.Bijective
      ((fderiv ℂ F (z,φ)).comp (ContinuousLinearMap.inl ℂ ℂ (CoeffPair p))) := by
    rw [hpartial]
    constructor
    · intro x y hxy
      exact mul_right_cancel₀ hs (by simpa using hxy)
    · intro w
      refine ⟨w / deriv (periodOneBoundaryCharacteristic hp hp1 b φ) z,?_⟩
      exact div_mul_cancel₀ w hs
  obtain ⟨μ,hμ,hμz,hzero⟩ := NLS.ComplexAnalysis.exists_analytic_implicitBanachRoot F z φ hF hz hbij
  have hc : Continuous (fun t : ℂ × CoeffPair p =>
      deriv (periodOneBoundaryCharacteristic hp hp1 b t.2) t.1) :=
    continuousOn_univ.mp (NLS.ComplexAnalysis.continuousOn_spectral_deriv_of_analyticOnNhd
      F univ isOpen_univ (analyticOnNhd_periodOneBoundaryCharacteristic_joint hp hp1 b))
  have hne : ∀ᶠ ψ in 𝓝 φ, deriv (periodOneBoundaryCharacteristic hp hp1 b ψ) (μ ψ) ≠ 0 :=
    (hc.continuousAt.comp (hμ.continuousAt.prodMk continuousAt_id)).eventually_ne
      (by simpa only [Function.comp_apply,id_eq,hμz] using hs)
  obtain ⟨r,hr,han⟩ := hμ.exists_ball_analyticOnNhd
  obtain ⟨V,hVsub,hVo,hφV⟩ := _root_.mem_nhds_iff.mp (hzero.and hne)
  refine ⟨μ,V ∩ Metric.ball φ r,hVo.inter Metric.isOpen_ball,
    ⟨hφV,Metric.mem_ball_self hr⟩,hμz,han.mono inter_subset_right,?_⟩
  intro ψ hψ
  exact hVsub hψ.1

/-- Algebraic simplicity of the actual restricted operator constructs an
analytic local spectral branch, retaining algebraic multiplicity one. -/
theorem exists_local_analytic_sourceBoundary_eigenvalue
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition)
    (φ : CoeffPair p) (z : ℂ)
    (hz : z ∈ b.spectrum hp (periodOneBoundaryPotential hp hp1 φ).val
      (periodOneBoundaryPotential hp hp1 φ).property)
    (hs : b.algebraicMultiplicity hp (periodOneBoundaryPotential hp hp1 φ).val
      (periodOneBoundaryPotential hp hp1 φ).property z = 1) :
    ∃ μ : CoeffPair p → ℂ, ∃ U : Set (CoeffPair p),
      IsOpen U ∧ φ ∈ U ∧ μ φ = z ∧ AnalyticOnNhd ℂ μ U ∧
      ∀ ψ ∈ U, μ ψ ∈ b.spectrum hp (periodOneBoundaryPotential hp hp1 ψ).val
        (periodOneBoundaryPotential hp hp1 ψ).property ∧
        b.algebraicMultiplicity hp (periodOneBoundaryPotential hp hp1 ψ).val
          (periodOneBoundaryPotential hp hp1 ψ).property (μ ψ) = 1 := by
  obtain ⟨μ,U,hU,hφ,hμ,han,hzeros⟩ := exists_local_analytic_sourceBoundary_zero hp hp1 b φ z
    ((periodOneBoundaryCharacteristic_eq_zero_iff hp hp1 b φ z).mpr hz)
    (deriv_periodOneBoundaryCharacteristic_ne_zero_of_multiplicity_one hp hp1 b φ z hs)
  refine ⟨μ,U,hU,hφ,hμ,han,?_⟩
  intro ψ hψ
  obtain ⟨hzero,hderiv⟩ := hzeros ψ hψ
  refine ⟨(periodOneBoundaryCharacteristic_eq_zero_iff hp hp1 b ψ (μ ψ)).mp hzero,?_⟩
  have ho := (analyticOnNhd_periodOneBoundaryCharacteristic hp hp1 b ψ (μ ψ)
    (mem_univ _)).analyticOrderAt_eq_one_of_zero_deriv_ne_zero hzero hderiv
  rw [analyticOrderAt_periodOneBoundaryCharacteristic] at ho
  exact_mod_cast ho

/-- The local branch through any simple Dirichlet zero obeys the exact
discriminant identity throughout its source neighborhood. -/
theorem sourceLemma9_2_local_analytic_branch
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) (z : ℂ)
    (hz : periodOneBoundaryCharacteristic hp hp1 .dirichlet φ z = 0)
    (hs : deriv (periodOneBoundaryCharacteristic hp hp1 .dirichlet φ) z ≠ 0) :
    ∃ μ : CoeffPair p → ℂ, ∃ U : Set (CoeffPair p),
      IsOpen U ∧ φ ∈ U ∧ μ φ = z ∧ AnalyticOnNhd ℂ μ U ∧
      ∀ ψ ∈ U, periodOneBoundaryCharacteristic hp hp1 .dirichlet ψ (μ ψ) = 0 ∧
        (canonicalDiscriminant hp (periodOnePotential ψ) (μ ψ))^2-4 =
          (sourceAntiDiscriminantCandidate hp hp1 ψ (μ ψ))^2 := by
  obtain ⟨μ,U,hU,hφ,hμ,han,hzeros⟩ := exists_local_analytic_sourceBoundary_zero hp hp1 .dirichlet φ z hz hs
  exact ⟨μ,U,hU,hφ,hμ,han,fun ψ hψ => ⟨(hzeros ψ hψ).1,
    sourceLemma9_2_identity hp hp1 ψ (μ ψ) (hzeros ψ hψ).1⟩⟩

end NLS.ZakharovShabat
