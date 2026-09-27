import NLS.ZakharovShabat.SourceNormalizedActionCircleKernel
import NLS.ZakharovShabat.SourceCriticalGapQuotientAnalytic
import NLS.ZakharovShabat.SourceCriticalRootRatioJointExteriorAnalytic
import NLS.ZakharovShabat.SourceStandardRootJointAnalytic
import NLS.ComplexAnalysis.ParametricCircleIntegral

/-!
# Source differentiability of the normalized action contour candidate

The rationalized kernel from the fixed-circle factorization has no
squared-gap denominator. All of its parameters and its deleted factor
are jointly analytic near a real-type source and an exterior spectral
point. Compactness of an isolating circle then gives a common analytic
tube and permits differentiation of the candidate in the source.
Restriction to every complex affine source line is analytic.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The source-dependent rationalized kernel, multiplied by the
deleted spectral factor. -/
def sourceNormalizedActionCircleIntegrandJoint
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) :
    ℂ × CoeffPair p → ℂ := fun t =>
  normalizedActionCircleKernel
    (canonicalPeriodicMidpoint hp hp1 (periodOnePotential t.2)
      (periodOnePotential_mem t.2) n)
    ((sourcePeriodicGapDisplacement hp hp1 t.2 n)^2)
    (canonicalCriticalGapQuotient hp hp1
      (periodOnePotential t.2) (periodOnePotential_mem t.2) n)
    t.1 * sourceCriticalRootRatioExtension hp hp1 n t.2 t.1

/-- Joint analyticity of the rationalized kernel at an exterior
point over a real-type source, including collapsed selected gaps. -/
theorem analyticAt_sourceNormalizedActionCircleIntegrandJoint_of_realType
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (z : ℂ) (hz : z ∈ sourceCanonicalRootDomain hp hp1 φ) :
    AnalyticAt ℂ (sourceNormalizedActionCircleIntegrandJoint hp hp1 n) (z,φ) := by
  let τ (ψ : CoeffPair p) := canonicalPeriodicMidpoint hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  let q (ψ : CoeffPair p) := (sourcePeriodicGapDisplacement hp hp1 ψ n)^2
  let B (ψ : CoeffPair p) := canonicalCriticalGapQuotient hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  let W (t : ℂ × CoeffPair p) := sourceStandardRoot hp hp1 t.2 n t.1
  let E (t : ℂ × CoeffPair p) :=
    sourceCriticalRootRatioExtension hp hp1 n t.2 t.1
  have hrootfun (ψ : CoeffPair p) (w : ℂ) :
      sourceStandardRoot hp hp1 ψ n w = normalizedStandardRoot (τ ψ) (q ψ) w := by
    simp only [sourceStandardRoot, τ, q, sourcePeriodicGapDisplacement_apply]
  obtain ⟨U,_,_,hreal,hdata⟩ :=
    exists_global_source_analytic_midpoint_squaredGap hp hp1
  have hτ : AnalyticAt ℂ τ φ := (hdata φ (hreal hφ) n).1
  have hq : AnalyticAt ℂ q φ := by
    simpa only [q, sourcePeriodicGapDisplacement_apply] using
      (hdata φ (hreal hφ) n).2
  have hB : AnalyticAt ℂ B φ :=
    analyticAt_sourceCriticalGapQuotient_apply_of_realType hp hp1 φ hφ n
  have hτj : AnalyticAt ℂ (fun t : ℂ × CoeffPair p => τ t.2) (z,φ) :=
    hτ.comp (analyticAt_snd (p := (z,φ)))
  have hqj : AnalyticAt ℂ (fun t : ℂ × CoeffPair p => q t.2) (z,φ) :=
    hq.comp (analyticAt_snd (p := (z,φ)))
  have hBj : AnalyticAt ℂ (fun t : ℂ × CoeffPair p => B t.2) (z,φ) :=
    hB.comp (analyticAt_snd (p := (z,φ)))
  have hW : AnalyticAt ℂ W (z,φ) := by
    exact sourceStandardRoot_joint_analyticAt_of_symmetric hp hp1 φ n z
      hτ (by simpa only [q, sourcePeriodicGapDisplacement_apply] using hq)
      (hz n)
  have hWne : W (z,φ) ≠ 0 :=
    sourceStandardRoot_ne_zero_off_segment hp hp1 φ n z (hz n)
  have hτne : τ φ ≠ z := by
    intro he
    exact (hz n) (he.symm ▸ sourcePeriodicMidpoint_mem_segment hp hp1 φ n)
  have hplus : τ φ-z+W (z,φ) ≠ 0 := by
    rw [show W (z,φ) = normalizedStandardRoot (τ φ) (q φ) z from
      hrootfun φ z]
    exact normalizedStandardRoot_add_ne_zero (τ φ) (q φ) z hτne
  have hd : AnalyticAt ℂ
      (fun t : ℂ × CoeffPair p => τ t.2-t.1) (z,φ) :=
    hτj.sub analyticAt_fst
  have hsum : AnalyticAt ℂ
      (fun t : ℂ × CoeffPair p => 4*(τ t.2-t.1+W t)) (z,φ) :=
    analyticAt_const.mul (hd.add hW)
  have hsumne : (4:ℂ)*(τ φ-z+W (z,φ)) ≠ 0 :=
    mul_ne_zero (by norm_num) hplus
  have hK : AnalyticAt ℂ (fun t : ℂ × CoeffPair p =>
      ((τ t.2-t.1)/(4*(τ t.2-t.1+W t)) +
        2*(τ t.2-t.1)*B t.2 + q t.2*(B t.2)^2)/W t) (z,φ) := by
    exact (((hd.div hsum hsumne).add
      ((analyticAt_const.mul hd).mul hBj)).add
        (hqj.mul (hBj.pow 2))).div hW hWne
  have hE : AnalyticAt ℂ E (z,φ) :=
    analyticAt_sourceCriticalRootRatioExtension_jointExterior hp hp1 n φ hφ z hz
  have hfun : sourceNormalizedActionCircleIntegrandJoint hp hp1 n =
      (fun t : ℂ × CoeffPair p =>
        ((τ t.2-t.1)/(4*(τ t.2-t.1+W t)) +
          2*(τ t.2-t.1)*B t.2 + q t.2*(B t.2)^2)/W t * E t) := by
    funext t
    simp only [sourceNormalizedActionCircleIntegrandJoint,
      normalizedActionCircleKernel, τ, q, B, W, E,
      sourceStandardRoot, sourcePeriodicGapDisplacement_apply]
  rw [hfun]
  exact hK.mul hE

/-- The source-dependent normalized-action candidate on a chosen
fixed circle. It remains defined at every collapsed gap. -/
def sourceNormalizedActionCircleCandidate
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (c : ℂ) (R : ℝ) (ψ : CoeffPair p) : ℂ :=
  normalizedActionCircleQuotient
    (canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n)
    ((sourcePeriodicGapDisplacement hp hp1 ψ n)^2)
    (canonicalCriticalGapQuotient hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) n)
    c R (sourceCriticalRootRatioExtension hp hp1 n ψ)

theorem sourceNormalizedActionCircleCandidate_eq_integral
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (c : ℂ) (R : ℝ) (ψ : CoeffPair p) :
    sourceNormalizedActionCircleCandidate hp hp1 n c R ψ =
      -(Real.pi : ℂ)⁻¹ *
        ∮ z in C(c,R), sourceNormalizedActionCircleIntegrandJoint
          hp hp1 n (z,ψ) := by
  rfl

/-- On one complex neighborhood of each real-type source, a fixed
circle gives both a differentiable normalized-action candidate and
an exact action factorization through the squared gap. -/
theorem exists_local_sourceNormalizedActionCircleCandidate_factor_differentiableOn
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (n : ℤ) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧
        DifferentiableOn ℂ
          (sourceNormalizedActionCircleCandidate hp hp1 n c R) V ∧
        ∀ ψ ∈ V,
          sourceActionCircle hp hp1 ψ c R =
            (sourcePeriodicGapDisplacement hp hp1 ψ n)^2 *
              sourceNormalizedActionCircleCandidate hp hp1 n c R ψ := by
  obtain ⟨V₀,hV₀open,hφV₀,c,R,hR,hgeom,hzero⟩ :=
    exists_local_sourceCriticalRootRatio_circleIntegral_zero_allGaps
      hp hp1 φ hφ n
  let F := sourceNormalizedActionCircleIntegrandJoint hp hp1 n
  let D : Set (ℂ × CoeffPair p) := {t | AnalyticAt ℂ F t}
  have hDopen : IsOpen D := isOpen_analyticAt ℂ F
  have hF : AnalyticOnNhd ℂ F D := fun _ ht => ht
  have hcircle (z : ℂ) (hz : z ∈ sphere c R) : (z,φ) ∈ D := by
    have hgeomφ := hgeom φ hφV₀
    have hdom : z ∈ sourceCanonicalRootDomain hp hp1 φ :=
      sourceCanonicalRootDomain_of_enclosingCircle hp hp1 φ n c R
        hgeomφ.1 hgeomφ.2 hz
    exact analyticAt_sourceNormalizedActionCircleIntegrandJoint_of_realType
      hp hp1 n φ hφ z hdom
  obtain ⟨V₁,hV₁open,hφV₁,M,_,hbound⟩ :=
    NLS.ComplexAnalysis.exists_uniform_joint_fderiv_bound_on_circle
      F D hDopen hF c R φ hcircle
  obtain ⟨W₁,hW₁open,hreal₁,hEdata⟩ :=
    exists_global_sourceCriticalRootRatioExtension_analytic hp hp1
  obtain ⟨W₂,hW₂open,_,hreal₂,hexact⟩ :=
    exists_global_sourceCriticalPoints_midpoint_gap_sq_exact hp hp1
  let V := ((V₀ ∩ V₁) ∩ W₁) ∩ W₂
  have hVopen : IsOpen V :=
    ((hV₀open.inter hV₁open).inter hW₁open).inter hW₂open
  have hφV : φ ∈ V :=
    ⟨⟨⟨hφV₀,hφV₁⟩,hreal₁ hφ⟩,hreal₂ hφ⟩
  refine ⟨V,hVopen,hφV,c,R,hR,?_,?_⟩
  · intro ψ hψ
    have hdom : ∀ b ∈ V, ∀ θ : ℝ,
        (circleMap c R θ,b) ∈ D := by
      intro b hb θ
      exact (hbound (circleMap c R θ)
        (circleMap_mem_sphere c hR.le θ) b hb.1.1.2).1
    have hdbound : ∀ b ∈ V, ∀ θ : ℝ,
        ‖fderiv ℂ F (circleMap c R θ,b)‖ ≤ M := by
      intro b hb θ
      exact (hbound (circleMap c R θ)
        (circleMap_mem_sphere c hR.le θ) b hb.1.1.2).2
    have hdiff := NLS.ComplexAnalysis.differentiableAt_circleIntegral_of_jointAnalytic
      F D hDopen hF c R hR.le V hVopen ψ hψ M hdom hdbound
    have hfun : sourceNormalizedActionCircleCandidate hp hp1 n c R =
        (fun b : CoeffPair p => -(Real.pi : ℂ)⁻¹ *
          ∮ z in C(c,R), F (z,b)) := by
      funext b
      exact sourceNormalizedActionCircleCandidate_eq_integral hp hp1 n c R b
    rw [hfun]
    exact (hdiff.const_mul (-(Real.pi : ℂ)⁻¹)).differentiableWithinAt
  · intro ψ hψ
    obtain ⟨hseg,hother⟩ := hgeom ψ hψ.1.1.1
    have hcircleψ : sphere c R ⊆ sourceCanonicalRootDomain hp hp1 ψ :=
      sourceCanonicalRootDomain_of_enclosingCircle hp hp1 ψ n c R hseg hother
    have hzseg : ∀ z ∈ sphere c R,
        z ∉ sourcePeriodicSegment hp hp1 ψ n := by
      intro z hz
      exact hcircleψ hz n
    have hE : AnalyticOnNhd ℂ
        (sourceCriticalRootRatioExtension hp hp1 n ψ) (closedBall c R) := by
      intro z hz
      exact hEdata ψ hψ.1.2 n z (hother hz)
    exact sourceActionCircle_eq_squaredGap_mul_kernel hp hp1 ψ n c R
      (canonicalCriticalGapQuotient hp hp1
        (periodOnePotential ψ) (periodOnePotential_mem ψ) n)
      hR.le hcircleψ hzseg (hzero ψ hψ.1.1.1) hE
      (hexact ψ hψ.2 n).2

/-- Restricting the normalized contour candidate to any complex
affine source line gives a one-variable analytic function at the
real-type base source, even when its gap is collapsed. -/
theorem exists_sourceNormalizedActionCircleCandidate_lineAnalyticAt
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (n : ℤ) :
    ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧
      ∀ h : CoeffPair p,
        AnalyticAt ℂ (fun t : ℂ =>
          sourceNormalizedActionCircleCandidate hp hp1 n c R (φ+t•h)) 0 := by
  obtain ⟨V,hVopen,hφV,c,R,hR,hdiff,_⟩ :=
    exists_local_sourceNormalizedActionCircleCandidate_factor_differentiableOn
      hp hp1 φ hφ n
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
      (fun t : ℂ => sourceNormalizedActionCircleCandidate hp hp1 n c R (a t)) U := by
    intro t ht
    exact (((hdiff (a t) ht).differentiableAt (hVopen.mem_nhds ht)).comp t
      (ha t)).differentiableWithinAt
  exact hline.analyticAt (hUopen.mem_nhds h0)

end NLS.ZakharovShabat
