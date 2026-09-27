import NLS.ZakharovShabat.SourceNormalizedActionUniformTailCircles
import NLS.ZakharovShabat.SourceCriticalRootRatioAnyCircleZero
import Mathlib.Analysis.Analytic.Uniqueness

/-!
# Vanishing of distant free-circle quotient periods on one source ball

The unweighted discriminant-derivative quotient has zero integral on
each fixed isolating circle near a real-type source. A common family
of free-centered circles stays valid on one source ball. Analyticity
of each contour integral and the identity principle extend the zero
throughout that same ball, uniformly in the distant index.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- One complex source ball and one cutoff make the unweighted
critical-root quotient integral vanish on every distant free circle. -/
theorem exists_local_source_distantCriticalRootRatio_freeCircle_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ)) :
    ∃ K : ℕ, ∃ r : ℝ, 0 < r ∧
      ∀ ψ ∈ ball φ r, ∀ n : ℤ, K ≤ n.natAbs →
        (∮ z in C((Real.pi:ℂ)*n,Real.pi/8),
          sourceCriticalRootRatioJoint hp hp1 (z,ψ)) = 0 := by
  obtain ⟨K,Vg,hVgopen,hφVg,hgeom⟩ :=
    exists_local_sourceNormalizedAction_uniform_tail_circle_data
      hp hp1 φ hreal
  obtain ⟨W,hWopen,_,hrealW,hDopen,hquot⟩ :=
    exists_global_sourceCriticalRootRatio_jointAnalytic hp hp1
  obtain ⟨r,hr,hrsub⟩ := Metric.mem_nhds_iff.mp
    ((hVgopen.inter hWopen).mem_nhds ⟨hφVg,hrealW hreal⟩)
  refine ⟨K,r,hr,?_⟩
  intro ψ hψ n hn
  let c : ℂ := (Real.pi:ℂ)*n
  let R : ℝ := Real.pi/8
  let G : CoeffPair p → ℂ := fun χ =>
    ∮ z in C(c,R), sourceCriticalRootRatioJoint hp hp1 (z,χ)
  have hgeomB (χ : CoeffPair p) (hχ : χ ∈ ball φ r) :
      sourcePeriodicSegment hp hp1 χ n ⊆ ball c R ∧
      closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 χ n := by
    obtain ⟨hseg,hother,_,_,_⟩ := hgeom χ (hrsub hχ).1 n hn
    exact ⟨hseg,hother⟩
  obtain ⟨U,hUopen,hφU,_,hzero⟩ :=
    exists_local_sourceCriticalRootRatio_circleIntegral_zero_on_givenCircle
      hp hp1 φ hreal n (ball φ r) Metric.isOpen_ball
      (mem_ball_self hr) c R (by positivity) hgeomB
  have hlocal : G =ᶠ[𝓝 φ] (fun _ => 0) := by
    filter_upwards [hUopen.mem_nhds hφU] with χ hχ
    exact hzero χ hχ
  have hGdiff : DifferentiableOn ℂ G (ball φ r) := by
    intro χ hχ
    have hcircle (z : ℂ) (hz : z ∈ sphere c R) :
        (z,χ) ∈ sourceCanonicalRootJointDomain hp hp1 W := by
      obtain ⟨hseg,hother⟩ := hgeomB χ hχ
      exact ⟨(hrsub hχ).2,
        sourceCanonicalRootDomain_of_enclosingCircle hp hp1 χ n c R
          hseg hother hz⟩
    obtain ⟨V,hVopen,hχV,M,_,hbound⟩ :=
      NLS.ComplexAnalysis.exists_uniform_joint_fderiv_bound_on_circle
        (sourceCriticalRootRatioJoint hp hp1)
        (sourceCanonicalRootJointDomain hp hp1 W)
        hDopen hquot c R χ hcircle
    have hdom : ∀ b ∈ V, ∀ θ : ℝ,
        (circleMap c R θ,b) ∈ sourceCanonicalRootJointDomain hp hp1 W := by
      intro b hb θ
      exact (hbound (circleMap c R θ)
        (circleMap_mem_sphere c (by positivity : 0 ≤ R) θ) b hb).1
    have hdbound : ∀ b ∈ V, ∀ θ : ℝ,
        ‖fderiv ℂ (sourceCriticalRootRatioJoint hp hp1)
          (circleMap c R θ,b)‖ ≤ M := by
      intro b hb θ
      exact (hbound (circleMap c R θ)
        (circleMap_mem_sphere c (by positivity : 0 ≤ R) θ) b hb).2
    exact (NLS.ComplexAnalysis.differentiableAt_circleIntegral_of_jointAnalytic
      (sourceCriticalRootRatioJoint hp hp1)
      (sourceCanonicalRootJointDomain hp hp1 W)
      hDopen hquot c R (by positivity : 0 ≤ R)
      V hVopen χ hχV M hdom hdbound).differentiableWithinAt
  let h : CoeffPair p := ψ-φ
  let a : ℂ → CoeffPair p := fun t => φ+t•h
  have ha : Differentiable ℂ a := by
    dsimp [a]
    fun_prop
  let T : Set ℂ := a ⁻¹' ball φ r
  have hTopen : IsOpen T := Metric.isOpen_ball.preimage ha.continuous
  have h0 : (0:ℂ) ∈ T := by
    simpa [T,a] using (mem_ball_self hr : φ ∈ ball φ r)
  have h1 : (1:ℂ) ∈ T := by
    have ha1 : a 1 = ψ := by dsimp [a,h]; module
    change a 1 ∈ ball φ r
    rw [ha1]
    exact hψ
  have hTconv : Convex ℝ T := by
    intro z hz w hw α β hα hβ hab
    have hcomb := (convex_ball φ r) hz hw hα hβ hab
    change a (α • z + β • w) ∈ ball φ r
    convert hcomb using 1
    dsimp [a]
    have habC : (α:ℂ)+(β:ℂ)=1 := by exact_mod_cast hab
    have hφeq : φ = (α:ℂ) • φ + (β:ℂ) • φ := by
      rw [← add_smul,habC,one_smul]
    conv_lhs => rw [hφeq]
    module
  have hGline : DifferentiableOn ℂ (fun t => G (a t)) T := by
    intro t ht
    exact (((hGdiff (a t) ht).differentiableAt
      (Metric.isOpen_ball.mem_nhds ht)).comp t (ha t)).differentiableWithinAt
  have hlineZero : (fun t => G (a t)) =ᶠ[𝓝 (0:ℂ)] (fun _ => 0) := by
    have hevent : ∀ᶠ t in 𝓝 (0:ℂ), a t ∈ U :=
      ha.continuous.continuousAt.eventually
        (hUopen.mem_nhds (by simpa [a] using hφU))
    filter_upwards [hevent] with t ht
    exact hzero (a t) ht
  have hEq := (hGline.analyticOnNhd hTopen).eqOn_of_preconnected_of_eventuallyEq
    analyticOnNhd_const hTconv.isPreconnected h0 hlineZero
  simpa [a,h,G,c,R] using hEq h1

end NLS.ZakharovShabat
