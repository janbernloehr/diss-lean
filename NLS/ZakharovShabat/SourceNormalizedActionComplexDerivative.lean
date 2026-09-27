import NLS.ZakharovShabat.SourceNormalizedActionComplexExtension
import NLS.ComplexAnalysis.ParametricCircleIntegral

/-!
# Source derivative of the complex normalized action

Near each real-type source, the chart-independent normalized action
is represented by a fixed isolating circle. Its Fréchet derivative is
the circle integral of the source derivative of the rationalized
kernel, including at a collapsed selected gap. The same circle and
formula work throughout a complex neighborhood of the base source.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A fixed-circle formula for the source derivative of the
chart-independent normalized action, valid also on the complex
collapsed-gap locus. -/
theorem exists_local_sourceNormalizedActionComplexExtension_fderiv_circle
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (n : ℤ) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ φ ∈ W ∧
      ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧
        ∀ ψ ∈ W, ∀ h : CoeffPair p,
          (fderiv ℂ (sourceNormalizedActionComplexExtension hp hp1 n) ψ) h =
            -(Real.pi : ℂ)⁻¹ *
              ∮ z in C(c,R),
                (fderiv ℂ
                  (fun χ : CoeffPair p =>
                    sourceNormalizedActionCircleIntegrandJoint hp hp1 n (z,χ))
                  ψ) h := by
  obtain ⟨U,hUopen,hφU,c,R,hR,hgeom,hdiff,hdata⟩ :=
    exists_local_sourceNormalizedActionCircleCandidate_eq_realExtension
      hp hp1 φ hφ n
  let F := sourceNormalizedActionCircleIntegrandJoint hp hp1 n
  let D : Set (ℂ × CoeffPair p) := {t | AnalyticAt ℂ F t}
  have hDopen : IsOpen D := isOpen_analyticAt ℂ F
  have hF : AnalyticOnNhd ℂ F D := fun _ ht => ht
  have hcircle (z : ℂ) (hz : z ∈ sphere c R) : (z,φ) ∈ D := by
    obtain ⟨hseg,hother⟩ := hgeom φ hφU
    have hdom : z ∈ sourceCanonicalRootDomain hp hp1 φ :=
      sourceCanonicalRootDomain_of_enclosingCircle hp hp1 φ n c R
        hseg hother hz
    exact analyticAt_sourceNormalizedActionCircleIntegrandJoint_of_realType
      hp hp1 n φ hφ z hdom
  obtain ⟨V,hVopen,hφV,M,_,hbound⟩ :=
    exists_uniform_joint_fderiv_bound_on_circle
      F D hDopen hF c R φ hcircle
  let W := U ∩ V
  have hWopen : IsOpen W := hUopen.inter hVopen
  have hφW : φ ∈ W := ⟨hφU,hφV⟩
  have hdom : ∀ b ∈ W, ∀ θ : ℝ, (circleMap c R θ,b) ∈ D := by
    intro b hb θ
    exact (hbound (circleMap c R θ)
      (circleMap_mem_sphere c hR.le θ) b hb.2).1
  have hdbound : ∀ b ∈ W, ∀ θ : ℝ,
      ‖fderiv ℂ F (circleMap c R θ,b)‖ ≤ M := by
    intro b hb θ
    exact (hbound (circleMap c R θ)
      (circleMap_mem_sphere c hR.le θ) b hb.2).2
  let J : CoeffPair p → ℂ := fun b => ∮ z in C(c,R), F (z,b)
  let A := sourceNormalizedActionCircleCandidate hp hp1 n c R
  let E := sourceNormalizedActionComplexExtension hp hp1 n
  have hA : A = fun b => -(Real.pi : ℂ)⁻¹ * J b := by
    funext b
    exact sourceNormalizedActionCircleCandidate_eq_integral hp hp1 n c R b
  have hEq : EqOn A E U := fun ψ hψ => (hdata ψ hψ).2.2
  refine ⟨W,hWopen,hφW,c,R,hR,?_⟩
  intro ψ hψ h
  have hJdiff : DifferentiableAt ℂ J ψ :=
    differentiableAt_circleIntegral_of_jointAnalytic F D hDopen hF
      c R hR.le W hWopen ψ hψ M hdom hdbound
  have hlocal : E =ᶠ[𝓝 ψ] A := by
    filter_upwards [hUopen.mem_nhds hψ.1] with χ hχ
    exact (hEq hχ).symm
  have hfderiv : fderiv ℂ E ψ = fderiv ℂ A ψ := hlocal.fderiv_eq
  rw [hfderiv, hA, fderiv_const_mul hJdiff]
  change (-(Real.pi : ℂ)⁻¹ • fderiv ℂ J ψ) h = _
  rw [smul_apply]
  simp only [smul_eq_mul]
  congr 1
  exact fderiv_circleIntegral_apply_of_jointAnalytic F D hDopen hF
    c R hR.le W hWopen ψ hψ M hdom hdbound h

end NLS.ZakharovShabat
