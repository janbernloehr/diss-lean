import NLS.ZakharovShabat.SourceCriticalRootRatioCircleDerivativeBound
import NLS.ComplexAnalysis.ParametricCircleIntegral

/-!
# Holomorphic dependence of the fixed gap contour integral

The critical-root quotient is jointly analytic on the moving-gap
complement. A fixed enclosing circle and its uniform source derivative
bound permit differentiation under the contour integral near any
real-type potential.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Near a real-type potential, a fixed circle encloses the selected
gap and its critical-root quotient integral is complex Fréchet
differentiable in the source potential. -/
theorem exists_local_sourceCriticalRootRatio_circleIntegral_differentiableOn
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (n : ℤ) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧
        (∀ ψ ∈ V,
          sourcePeriodicSegment hp hp1 ψ n ⊆ ball c R ∧
          closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n) ∧
        DifferentiableOn ℂ
          (fun ψ : CoeffPair p =>
            ∮ z in C(c, R), sourceCriticalRootRatioJoint hp hp1 (z,ψ)) V := by
  obtain ⟨W, hWopen, _, hreal, hDopen, hquot⟩ :=
    exists_global_sourceCriticalRootRatio_jointAnalytic hp hp1
  obtain ⟨V₀, hV₀open, hφV₀, c, R, M, hR, _, hdata⟩ :=
    exists_local_sourceCriticalRootRatio_circleDerivativeBound hp hp1 φ hφ n
  let V := V₀ ∩ W
  have hVopen : IsOpen V := hV₀open.inter hWopen
  have hφV : φ ∈ V := ⟨hφV₀, hreal hφ⟩
  have hcircle (ψ : CoeffPair p) (hψ : ψ ∈ V) :
      sphere c R ⊆ sourceCanonicalRootDomain hp hp1 ψ := by
    obtain ⟨hseg,hother,_⟩ := hdata ψ hψ.1
    exact sourceCanonicalRootDomain_of_enclosingCircle hp hp1 ψ n c R hseg hother
  refine ⟨V, hVopen, hφV, c, R, hR, ?_, ?_⟩
  · intro ψ hψ
    obtain ⟨hseg,hother,_⟩ := hdata ψ hψ.1
    exact ⟨hseg,hother⟩
  · intro ψ hψ
    have hdiff :=
      NLS.ComplexAnalysis.differentiableAt_circleIntegral_of_jointAnalytic
        (sourceCriticalRootRatioJoint hp hp1)
        (sourceCanonicalRootJointDomain hp hp1 W)
        hDopen hquot c R hR.le V hVopen ψ hψ M
        (fun b hb θ =>
          ⟨hb.2, hcircle b hb (circleMap_mem_sphere c hR.le θ)⟩)
        (fun b hb θ =>
          ((hdata b hb.1).2.2 (circleMap c R θ)
            (circleMap_mem_sphere c hR.le θ)).1)
    exact hdiff.differentiableWithinAt

/-- Restricting the fixed-contour integral to any complex affine line
through a real-type source gives a one-variable analytic function near
the base source. -/
theorem exists_sourceCriticalRootRatio_circleIntegral_lineAnalyticAt
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (n : ℤ) :
    ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧
      ∀ h : CoeffPair p,
        AnalyticAt ℂ (fun t : ℂ =>
          ∮ z in C(c, R), sourceCriticalRootRatioJoint hp hp1 (z,φ+t•h)) 0 := by
  obtain ⟨V, hVopen, hφV, c, R, hR, _, hdiff⟩ :=
    exists_local_sourceCriticalRootRatio_circleIntegral_differentiableOn
      hp hp1 φ hφ n
  refine ⟨c, R, hR, ?_⟩
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
        ∮ z in C(c, R), sourceCriticalRootRatioJoint hp hp1 (z,a t)) U := by
    intro t ht
    exact (((hdiff (a t) ht).differentiableAt (hVopen.mem_nhds ht)).comp t
      (ha t)).differentiableWithinAt
  exact hline.analyticAt (hUopen.mem_nhds h0)

end NLS.ZakharovShabat
