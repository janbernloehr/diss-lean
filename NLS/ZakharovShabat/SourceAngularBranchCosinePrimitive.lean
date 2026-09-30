import NLS.ZakharovShabat.SourceAngularComplexDirichletAngle
import NLS.ComplexAnalysis.ParametricCosineChart

/-! # Actual angular primitives on analytic half-gap branches

Construct jointly analytic cosine primitives at arbitrary complex open
gaps. Their endpoints are the actual unordered periodic pair, while
the half-gap is an analytic local branch. No analyticity or continuity
of the canonical ordering is used.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def sourceAngularBranchCosinePrimitive (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (δ : CoeffPair p → ℂ) :
    ℂ × CoeffPair p → ℂ :=
  parametricCosinePrimitive (fun x => sourceAngularGapNumerator hp hp1 n m s x.2 x.1)
    (fun ψ => canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m) δ

@[simp] theorem sourceAngularBranchCosinePrimitive_pi
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (δ : CoeffPair p → ℂ) (ψ : CoeffPair p) :
    sourceAngularBranchCosinePrimitive hp hp1 n m s δ ((Real.pi : ℂ),ψ) = 0 :=
  parametricConvexPrimitive_anchor _ _ ψ

structure SourceAngularBranchCosineChartData (hp : p ≠ ⊤) (hp1 : 1 < p) (m : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (δ : CoeffPair p → ℂ)
    (W V : Set (CoeffPair p)) (Ω : Set ℂ) (c : ℤ → ℂ) (R : ℤ → ℝ) : Prop where
  source_open : IsOpen V
  source_subset : V ⊆ W
  angle_open : IsOpen Ω
  angle_convex : Convex ℝ Ω
  angle_segment : segment ℝ (0 : ℂ) (Real.pi : ℂ) ⊆ Ω
  midpoint_analytic : AnalyticOnNhd ℂ (fun ψ : CoeffPair p => canonicalPeriodicMidpoint hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) m) V
  halfGap_analytic : AnalyticOnNhd ℂ δ V
  halfGap_ne_zero : ∀ ψ ∈ V, δ ψ ≠ 0
  halfGap_sq : ∀ ψ ∈ V, δ ψ ^ 2 = (canonicalPeriodicGap hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) m / 2) ^ 2
  disc_family : ∀ ψ ∈ V, SourceAngularDirichletDiscFamilyData hp hp1 s ψ c R
  endpoint_data : ∀ ψ ∈ V, SourceAngularEndpointSpectralData hp hp1 ψ m
  omitted_analytic : AnalyticOnNhd ℂ (sourceStandardRootOmittedJointProduct hp hp1 m)
    (ball (c m) (R m) ×ˢ V)
  cosine_enclosed : ∀ ψ ∈ V, ∀ θ ∈ Ω,
    sourceAngularBranchCosinePoint hp hp1 m δ (θ,ψ) ∈ ball (c m) (R m)
  numerator_analytic : ∀ n : ℤ, AnalyticOnNhd ℂ (fun x : ℂ × CoeffPair p =>
    sourceAngularGapNumerator hp hp1 n m s x.2 (sourceAngularBranchCosinePoint hp hp1 m δ x)) (Ω ×ˢ V)
  primitive_analytic : ∀ n : ℤ, AnalyticOnNhd ℂ
    (sourceAngularBranchCosinePrimitive hp hp1 n m s δ) (Ω ×ˢ V)
  primitive_derivative : ∀ n : ℤ, ∀ ψ ∈ V, ∀ θ ∈ Ω,
    HasDerivAt (fun e => sourceAngularBranchCosinePrimitive hp hp1 n m s δ (e,ψ))
      (sourceAngularGapNumerator hp hp1 n m s ψ (sourceAngularBranchCosinePoint hp hp1 m δ (θ,ψ))) θ

namespace SourcePsiIsolatingComplexExtension
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ : Set (CoeffPair p)}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}

/-- Local assigned discs and symmetric spectral analyticity construct
the actual primitive family at every complex open gap in their domain. -/
theorem exists_local_branch_cosine_angular_primitives
    (hs : SourcePsiIsolatingComplexExtension hp hp1 W₀ s)
    (W O : Set (CoeffPair p)) (hW : IsOpen W) (hWW₀ : W ⊆ W₀)
    (hO : IsOpen O) (hOW : O ⊆ W)
    (c : ℤ → ℂ) (R : ℤ → ℝ)
    (hdiscs : ∀ ψ ∈ O, SourceAngularDirichletDiscFamilyData hp hp1 s ψ c R)
    (m : ℤ) (hτ : AnalyticOnNhd ℂ (fun ψ : CoeffPair p => canonicalPeriodicMidpoint hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) m) O)
    (φ : CoeffPair p) (hφ : φ ∈ O)
    (hγsq : AnalyticAt ℂ (fun ψ : CoeffPair p => (canonicalPeriodicGap hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) m) ^ 2) φ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) m ≠ 0)
    (hD : IsOpen (sourceStandardRootOmittedJointDomain hp hp1 W m))
    (hP : AnalyticOnNhd ℂ (sourceStandardRootOmittedJointProduct hp hp1 m)
      (sourceStandardRootOmittedJointDomain hp hp1 W m)) :
    ∃ V : Set (CoeffPair p), ∃ Ω : Set ℂ, ∃ δ : CoeffPair p → ℂ, φ ∈ V ∧
      δ φ = canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) m / 2 ∧
      SourceAngularBranchCosineChartData hp hp1 m s δ W V Ω c R := by
  obtain ⟨B,hB,hφB,hBO,δ,hδ,hbase,hroots⟩ :=
    exists_local_sourceAnalyticHalfGap hp hp1 O hO φ hφ m hgap hγsq
  let τ : CoeffPair p → ℂ := fun ψ => canonicalPeriodicMidpoint hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) m
  let D := (ball (c m) (R m) ×ˢ W) ∩ sourceStandardRootOmittedJointDomain hp hp1 W m
  have hDopen : IsOpen D := (isOpen_ball.prod hW).inter hD
  have hbaseGap : ∀ z ∈ segment ℝ (τ φ - δ φ) (τ φ + δ φ), (z,φ) ∈ D := by
    intro z hz
    rw [sourcePeriodicSegment_eq_of_halfGap_sq hp hp1 φ m (δ φ) (hroots φ hφB).2] at hz
    have hgeom := (hdiscs φ hφ).contour_family.2 m
    have hzball := hgeom.2.1 hz
    exact ⟨⟨hzball,hOW hφ⟩,hOW hφ,hgeom.2.2.1 (ball_subset_closedBall hzball)⟩
  obtain ⟨V,Ω,hV,hφV,hVB,hΩ,hconv,hangle,hchart⟩ :=
    exists_local_parametricCosine_chart τ δ B hB (hτ.mono hBO) hδ D hDopen φ hφB hbaseGap
  have hVO : V ⊆ O := hVB.trans hBO
  have hVW : V ⊆ W := hVO.trans hOW
  have hτV : AnalyticOnNhd ℂ τ V := hτ.mono hVO
  have hδV : AnalyticOnNhd ℂ δ V := hδ.mono hVB
  have hg (n : ℤ) := hs.angular_gapNumerator_analyticOnNhd_joint n m W hWW₀ hP
  have hmap : ∀ x ∈ Ω ×ˢ V, (cosineGapPoint (τ x.2) (δ x.2) x.1,x.2) ∈
      sourceStandardRootOmittedJointDomain hp hp1 W m := fun x hx => (hchart x.2 hx.2 x.1 hx.1).2
  have hendpoint (ψ : CoeffPair p) (hψ : ψ ∈ V) : SourceAngularEndpointSpectralData hp hp1 ψ m := by
    have hopen : IsOpen (sourceStandardRootOmittedDomain hp hp1 ψ m) := by
      have heq : sourceStandardRootOmittedDomain hp hp1 ψ m =
          (fun z : ℂ => (z,ψ)) ⁻¹' sourceStandardRootOmittedJointDomain hp hp1 W m := by
        ext z; exact ⟨fun hz => ⟨hVW hψ,hz⟩,And.right⟩
      rw [heq]
      exact hD.preimage (continuous_id.prodMk continuous_const)
    have hgeom := (hdiscs ψ (hVO hψ)).contour_family.2 m
    exact ⟨hopen,(fun z hz => hgeom.2.2.1 (ball_subset_closedBall (hgeom.2.1 hz))),
      sourceStandardRootOmittedProduct_analyticOnNhd_spectral hp hp1 m W hP ψ (hVW hψ)⟩
  have hspec (n : ℤ) := parametricCosinePrimitive_spec _ τ δ _ Ω V hΩ hconv hV
    (hangle (right_mem_segment ℝ _ _)) (hg n) hτV hδV hmap
  exact ⟨V,Ω,δ,hφV,hbase,⟨hV,hVW,hΩ,hconv,hangle,hτV,hδV,
    (fun ψ hψ => (hroots ψ (hVB hψ)).1),(fun ψ hψ => (hroots ψ (hVB hψ)).2),
    (fun ψ hψ => hdiscs ψ (hVO hψ)),hendpoint,
    hP.mono (fun x hx => ⟨hVW hx.2,((hdiscs x.2 (hVO hx.2)).contour_family.2 m).2.2.1
      (ball_subset_closedBall hx.1)⟩),
    (fun ψ hψ θ hθ => (hchart ψ hψ θ hθ).1.1),
    (fun n => analyticOnNhd_parametricCosineNumerator _ τ δ _ Ω V (hg n) hτV hδV hmap),
    (fun n => (hspec n).1),(fun n ψ hψ θ hθ => (hspec n).2.2 ψ hψ θ hθ)⟩⟩

end SourcePsiIsolatingComplexExtension
end NLS.ZakharovShabat
