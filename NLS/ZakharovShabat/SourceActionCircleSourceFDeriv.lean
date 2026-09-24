import NLS.ZakharovShabat.SourceActionCircleAnalytic

/-!
# Source Fréchet derivative of a fixed-circle action

Differentiation under the circle integral gives an explicit
angle-integral formula for the source derivative of the weighted
critical-root quotient action. This is the derivative before the
spectral integration-by-parts simplification in Lemma 11.1.
-/

noncomputable section
open Set Metric Complex
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- On a complex neighborhood of any real-type source, the Fréchet
derivative of the fixed-circle action is the normalized angle
integral of the source derivative of its integrand. -/
theorem exists_local_sourceActionCircle_fderiv_formula
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (n : ℤ) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧
        (∀ ψ ∈ V,
          sourcePeriodicSegment hp hp1 ψ n ⊆ ball c R ∧
          closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n) ∧
        ∀ ψ ∈ V,
          fderiv ℂ (fun b : CoeffPair p =>
            sourceActionCircle hp hp1 b c R) ψ =
            (Real.pi : ℂ)⁻¹ •
              ∫ θ in (0:ℝ)..2*Real.pi,
                (deriv (circleMap c R) θ) •
                  (fderiv ℂ (sourceActionIntegrandJoint hp hp1)
                    (circleMap c R θ,ψ)).comp
                      (ContinuousLinearMap.inr ℂ ℂ (CoeffPair p)) := by
  obtain ⟨W,_,_,hWreal,hDopen,hweighted⟩ :=
    exists_global_sourceActionIntegrand_jointAnalytic hp hp1
  obtain ⟨V₀,hV₀open,hφV₀,c,R,hR,hgeom⟩ :=
    exists_local_sourceCriticalRootRatio_uniformEnclosingCircle
      hp hp1 φ hφ n
  have hcircle (z : ℂ) (hz : z ∈ sphere c R) :
      (z,φ) ∈ sourceCanonicalRootJointDomain hp hp1 W :=
    ⟨hWreal hφ,(hgeom φ hφV₀).2.2 hz⟩
  obtain ⟨V₁,hV₁open,hφV₁,M,_,hbound⟩ :=
    NLS.ComplexAnalysis.exists_uniform_joint_fderiv_bound_on_circle
      (sourceActionIntegrandJoint hp hp1)
      (sourceCanonicalRootJointDomain hp hp1 W)
      hDopen hweighted c R φ hcircle
  let V := V₀ ∩ V₁
  have hVopen : IsOpen V := hV₀open.inter hV₁open
  refine ⟨V,hVopen,⟨hφV₀,hφV₁⟩,c,R,hR,?_,?_⟩
  · intro ψ hψ
    obtain ⟨hseg,hother,_⟩ := hgeom ψ hψ.1
    exact ⟨hseg,hother⟩
  intro ψ hψ
  have hcircleDeriv :=
    NLS.ComplexAnalysis.hasFDerivAt_circleIntegral_of_jointAnalytic
      (sourceActionIntegrandJoint hp hp1)
      (sourceCanonicalRootJointDomain hp hp1 W)
      hDopen hweighted c R hR.le V hVopen ψ hψ M
      (fun b hb θ => (hbound (circleMap c R θ)
        (circleMap_mem_sphere c hR.le θ) b hb.2).1)
      (fun b hb θ => (hbound (circleMap c R θ)
        (circleMap_mem_sphere c hR.le θ) b hb.2).2)
  have haction := hcircleDeriv.const_mul (Real.pi : ℂ)⁻¹
  exact haction.fderiv

end NLS.ZakharovShabat
