import NLS.ZakharovShabat.SourceCriticalRootRatioJointAnalytic
import NLS.ComplexAnalysis.UniformJointDerivativeCircle

/-!
# A uniform source derivative bound on a fixed gap contour

The fixed enclosing circle near a real-type potential lies in the
joint analyticity domain of the critical-root quotient. Compactness
then bounds its source derivative uniformly around the entire contour.
-/

noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- On one source neighborhood, a fixed contour encloses the selected
gap, avoids all other gaps, and has a uniformly bounded source
Fréchet derivative of the quotient integrand. -/
theorem exists_local_sourceCriticalRootRatio_circleDerivativeBound
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (n : ℤ) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∃ c : ℂ, ∃ R M : ℝ, 0 < R ∧ 0 ≤ M ∧
        ∀ ψ ∈ V,
          sourcePeriodicSegment hp hp1 ψ n ⊆ ball c R ∧
          closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n ∧
          (∀ z ∈ sphere c R,
            ‖fderiv ℂ (sourceCriticalRootRatioJoint hp hp1) (z,ψ)‖ ≤ M ∧
            ‖fderiv ℂ (fun χ : CoeffPair p =>
              sourceCriticalRootRatioJoint hp hp1 (z,χ)) ψ‖ ≤ M) := by
  obtain ⟨W, _, _, hreal, hDopen, hquot⟩ :=
    exists_global_sourceCriticalRootRatio_jointAnalytic hp hp1
  obtain ⟨V₀, hV₀open, hφV₀, c, R, hR, hgeom⟩ :=
    exists_local_sourceCriticalRootRatio_uniformEnclosingCircle hp hp1 φ hφ n
  have hcircle (z : ℂ) (hz : z ∈ sphere c R) :
      (z,φ) ∈ sourceCanonicalRootJointDomain hp hp1 W :=
    ⟨hreal hφ, (hgeom φ hφV₀).2.2 hz⟩
  obtain ⟨V₁, hV₁open, hφV₁, M, hM, hbound⟩ :=
    NLS.ComplexAnalysis.exists_uniform_joint_fderiv_bound_on_circle
      (sourceCriticalRootRatioJoint hp hp1)
      (sourceCanonicalRootJointDomain hp hp1 W)
      hDopen hquot c R φ hcircle
  refine ⟨V₀ ∩ V₁, hV₀open.inter hV₁open, ⟨hφV₀,hφV₁⟩,
    c, R, M, hR, hM, ?_⟩
  intro ψ hψ
  obtain ⟨hseg,hother,_⟩ := hgeom ψ hψ.1
  refine ⟨hseg,hother,?_⟩
  intro z hz
  obtain ⟨hpoint,hjoint⟩ := hbound z hz ψ hψ.2
  exact ⟨hjoint,
    (NLS.ComplexAnalysis.norm_fderiv_parameter_section_le
      (sourceCriticalRootRatioJoint hp hp1) z ψ
      (hquot (z,ψ) hpoint).differentiableAt).trans hjoint⟩

end NLS.ZakharovShabat
