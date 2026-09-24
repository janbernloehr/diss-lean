import NLS.ZakharovShabat.SourceCriticalRootRatioCircleAllGaps
import NLS.ZakharovShabat.SourceCriticalRootRatioCollapsedContour

/-!
# The source action on a fixed isolating circle

Equation (2.16) of the dissertation defines the nth action by
integrating the spectral parameter times the critical-root quotient
around the nth periodic gap. We record that integral for a specified
circle, prove the recentering used in Lemma 11.1, and prove that it
vanishes at a collapsed gap. Contour independence and source
analyticity are separate steps.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The action integral of (2.16) on a specified positively oriented
circle. Its index is encoded by the choice of isolating circle. -/
def sourceActionCircle (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (c : ℂ) (R : ℝ) : ℂ :=
  (Real.pi : ℂ)⁻¹ *
    ∮ z in C(c,R), z * sourceCriticalRootRatioJoint hp hp1 (z,ψ)

/-- If the unweighted quotient integral vanishes, the action may be
recentered at any spectral point, especially the indexed critical
point. -/
theorem sourceActionCircle_eq_recentered
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hcircle : sphere c R ⊆ sourceCanonicalRootDomain hp hp1 ψ)
    (hzero : (∮ z in C(c,R), sourceCriticalRootRatioJoint hp hp1 (z,ψ)) = 0)
    (a : ℂ) :
    sourceActionCircle hp hp1 ψ c R =
      (Real.pi : ℂ)⁻¹ *
        ∮ z in C(c,R), (z-a) * sourceCriticalRootRatioJoint hp hp1 (z,ψ) := by
  let q : ℂ → ℂ := fun z => sourceCriticalRootRatioJoint hp hp1 (z,ψ)
  have hq : ContinuousOn q (sphere c R) := by
    intro z hz
    exact ((sourceCriticalRootRatio_analyticOnNhd hp hp1 ψ z
      (hcircle hz)).continuousAt).continuousWithinAt
  have hi : CircleIntegrable (fun z => z*q z) c R :=
    ContinuousOn.circleIntegrable hR (continuousOn_id.mul hq)
  have hconst : CircleIntegrable (fun z => a*q z) c R :=
    ContinuousOn.circleIntegrable hR (continuousOn_const.mul hq)
  have hrec :
      (∮ z in C(c,R), (z-a)*q z) =
        (∮ z in C(c,R), z*q z) := by
    calc
      _ = ∮ z in C(c,R), z*q z - a*q z := by
        apply circleIntegral.integral_congr hR
        intro z hz
        ring
      _ = (∮ z in C(c,R), z*q z) -
            ∮ z in C(c,R), a*q z := circleIntegral.integral_sub hi hconst
      _ = (∮ z in C(c,R), z*q z) := by
        rw [circleIntegral.integral_const_mul, show (∮ z in C(c,R), q z) = 0 from hzero]
        simp
  exact congrArg ((Real.pi : ℂ)⁻¹ * ·) hrec.symm

/-- On the common complex source neighborhood of any real-type base
potential, the action on the fixed isolating circle can be recentered
at every spectral point. -/
theorem exists_local_sourceActionCircle_eq_recentered
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (n : ℤ) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧
        (∀ ψ ∈ V,
          sourcePeriodicSegment hp hp1 ψ n ⊆ ball c R ∧
          closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n) ∧
        (∀ ψ ∈ V, ∀ a : ℂ,
          sourceActionCircle hp hp1 ψ c R =
            (Real.pi : ℂ)⁻¹ *
              ∮ z in C(c,R), (z-a) * sourceCriticalRootRatioJoint hp hp1 (z,ψ)) := by
  obtain ⟨V,hVopen,hφV,c,R,hR,hgeom,hzero⟩ :=
    exists_local_sourceCriticalRootRatio_circleIntegral_zero_allGaps
      hp hp1 φ hφ n
  refine ⟨V,hVopen,hφV,c,R,hR,hgeom,?_⟩
  intro ψ hψ a
  have hcircle : sphere c R ⊆ sourceCanonicalRootDomain hp hp1 ψ :=
    sourceCanonicalRootDomain_of_enclosingCircle hp hp1 ψ n c R
      (hgeom ψ hψ).1 (hgeom ψ hψ).2
  exact sourceActionCircle_eq_recentered hp hp1 ψ c R hR.le
    hcircle (hzero ψ hψ) a

/-- A collapsed selected gap contributes zero to the action integral
on any isolating circle. Analytic extension removes its apparent
singularity throughout the filled disc. -/
theorem exists_global_sourceActionCircle_zero_of_zeroGap
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧
      realTypeSourceLocus p ⊆ W ∧
      ∀ ψ ∈ W, ∀ n : ℤ,
        sourcePeriodicGapDisplacement hp hp1 ψ n = 0 →
          ∀ c : ℂ, ∀ R : ℝ, 0 ≤ R →
            closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n →
              sphere c R ⊆ sourceCanonicalRootDomain hp hp1 ψ →
                sourceActionCircle hp hp1 ψ c R = 0 := by
  obtain ⟨W,hWopen,hreal,hdata⟩ :=
    exists_global_sourceCriticalRootRatio_analytic_of_zeroGap hp hp1
  refine ⟨W,hWopen,hreal,?_⟩
  intro ψ hψ n hgap c R hR hfilled hcircle
  let f : ℂ → ℂ := sourceCriticalRootRatioExtension hp hp1 n ψ
  have hanalytic := (hdata ψ hψ n hgap).1
  have heq := (hdata ψ hψ n hgap).2
  have hweighted : AnalyticOnNhd ℂ (fun z : ℂ => z*f z) (closedBall c R) := by
    intro z hz
    exact analyticAt_id.mul (hanalytic z (hfilled hz))
  have hzero : (∮ z in C(c,R), z*f z) = 0 :=
    (hweighted.differentiableOn.diffContOnCl_ball subset_rfl).circleIntegral_eq_zero hR
  have hsame :
      (∮ z in C(c,R), z*sourceCriticalRootRatioJoint hp hp1 (z,ψ)) =
        ∮ z in C(c,R), z*f z := by
    apply circleIntegral.integral_congr hR
    intro z hz
    change z * (deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
      sourceCanonicalRoot hp hp1 ψ z) =
        z * sourceCriticalRootRatioExtension hp hp1 n ψ z
    rw [heq z (hcircle hz)]
  unfold sourceActionCircle
  rw [hsame,hzero,mul_zero]

end NLS.ZakharovShabat
