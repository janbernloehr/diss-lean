import NLS.ZakharovShabat.SourceCriticalRootRatioJointExteriorAnalytic
import NLS.ComplexAnalysis.ParametricCircleIntegral

/-!
# Source derivative of the deleted-factor contour integral

Joint analyticity of the deleted factor on a tube around a fixed
enclosing circle gives a uniform derivative bound there. The
parametric circle-integral theorem then differentiates the deleted
factor's contour integral in the complex source parameter.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A fixed contour integral of the deleted factor is complex
Fréchet differentiable throughout one source neighborhood of a
real-type potential. -/
theorem exists_local_sourceCriticalRootRatioExtension_circleIntegral_differentiableOn
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ)) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧
        (∀ ψ ∈ V,
          sourcePeriodicSegment hp hp1 ψ n ⊆ ball c R ∧
          sphere c R ⊆ sourceCanonicalRootDomain hp hp1 ψ) ∧
        DifferentiableOn ℂ (fun ψ : CoeffPair p =>
          ∮ z in C(c,R), sourceCriticalRootRatioExtension hp hp1 n ψ z) V := by
  obtain ⟨V₀,hV₀open,hφV₀,c,R,hR,U,hUopen,hKU,hgeom,hanalytic⟩ :=
    exists_local_sourceCriticalRootRatioExtension_analyticTube
      hp hp1 n φ hreal
  let E : ℂ × CoeffPair p → ℂ := fun t =>
    sourceCriticalRootRatioExtension hp hp1 n t.2 t.1
  let D : Set (ℂ × CoeffPair p) := U ×ˢ V₀
  have hDopen : IsOpen D := hUopen.prod hV₀open
  have hE : AnalyticOnNhd ℂ E D := by
    intro t ht
    exact hanalytic t.2 ht.2 t.1 ht.1
  have hcircle : ∀ z ∈ sphere c R, (z,φ) ∈ D := by
    intro z hz
    exact ⟨hKU hz,hφV₀⟩
  obtain ⟨V₁,hV₁open,hφV₁,M,_,hbound⟩ :=
    NLS.ComplexAnalysis.exists_uniform_joint_fderiv_bound_on_circle
      E D hDopen hE c R φ hcircle
  let V := V₀ ∩ V₁
  refine ⟨V,hV₀open.inter hV₁open,⟨hφV₀,hφV₁⟩,
    c,R,hR,?_,?_⟩
  · intro ψ hψ
    exact hgeom ψ hψ.1
  · intro ψ hψ
    have hdom : ∀ b ∈ V, ∀ θ : ℝ,
        (circleMap c R θ,b) ∈ D := by
      intro b hb θ
      exact ⟨hKU (circleMap_mem_sphere c hR.le θ),hb.1⟩
    have hdbound : ∀ b ∈ V, ∀ θ : ℝ,
        ‖fderiv ℂ E (circleMap c R θ,b)‖ ≤ M := by
      intro b hb θ
      exact (hbound (circleMap c R θ)
        (circleMap_mem_sphere c hR.le θ) b hb.2).2
    have hdiff :=
      NLS.ComplexAnalysis.differentiableAt_circleIntegral_of_jointAnalytic
        E D hDopen hE c R hR.le V
        (hV₀open.inter hV₁open) ψ hψ M hdom hdbound
    exact hdiff.differentiableWithinAt

/-- Along every complex affine source line through a real-type
potential, the same deleted-factor circle integral is analytic at
the base parameter. -/
theorem exists_sourceCriticalRootRatioExtension_circleIntegral_lineAnalyticAt
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ)) :
    ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧
      ∀ h : CoeffPair p,
        AnalyticAt ℂ (fun t : ℂ =>
          ∮ z in C(c,R), sourceCriticalRootRatioExtension
            hp hp1 n (φ+t•h) z) 0 := by
  obtain ⟨V,hVopen,hφV,c,R,hR,_,hdiff⟩ :=
    exists_local_sourceCriticalRootRatioExtension_circleIntegral_differentiableOn
      hp hp1 n φ hreal
  refine ⟨c,R,hR,?_⟩
  intro h
  let a : ℂ → CoeffPair p := fun t => φ+t•h
  have ha : Differentiable ℂ a := by
    dsimp [a]
    fun_prop
  let U : Set ℂ := a ⁻¹' V
  have hUopen : IsOpen U := hVopen.preimage ha.continuous
  have h0 : (0:ℂ) ∈ U := by simpa [U,a] using hφV
  have hline : DifferentiableOn ℂ
      (fun t : ℂ =>
        ∮ z in C(c,R), sourceCriticalRootRatioExtension
          hp hp1 n (a t) z) U := by
    intro t ht
    exact (((hdiff (a t) ht).differentiableAt
      (hVopen.mem_nhds ht)).comp t (ha t)).differentiableWithinAt
  exact hline.analyticAt (hUopen.mem_nhds h0)

end NLS.ZakharovShabat
