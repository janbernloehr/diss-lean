import NLS.ZakharovShabat.SourceCriticalRootRatioUniformCircle
import NLS.ComplexAnalysis.JointSpectralDerivative

/-!
# Joint analyticity of the critical-root contour integrand

The discriminant derivative is jointly analytic in the spectral
parameter and source potential. Dividing by the jointly analytic
canonical root therefore gives an analytic function off all moving
periodic gap segments.
-/

noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual quotient integrand as a function of both the spectral
parameter and source potential. -/
def sourceCriticalRootRatioJoint (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ℂ × CoeffPair p → ℂ :=
  fun t => deriv (canonicalDiscriminant hp (periodOnePotential t.2)) t.1 /
    sourceCanonicalRoot hp hp1 t.2 t.1

/-- The spectral derivative of the discriminant is jointly analytic
on the full spectral/source product. -/
theorem analyticOnNhd_sourceDiscriminantDerivative_joint
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    AnalyticOnNhd ℂ
      (fun t : ℂ × CoeffPair p =>
        deriv (canonicalDiscriminant hp (periodOnePotential t.2)) t.1)
      univ := by
  let F : ℂ × CoeffPair p → ℂ := fun t =>
    canonicalDiscriminant hp (periodOnePotential t.2) t.1
  have hF : AnalyticOnNhd ℂ F univ :=
    analyticOnNhd_canonicalDiscriminant_periodOne hp hp1
  let ev : ((ℂ × CoeffPair p) →L[ℂ] ℂ) →L[ℂ] ℂ :=
    ContinuousLinearMap.apply ℂ ℂ (1,0)
  have hderiv : AnalyticOnNhd ℂ
      (fun t : ℂ × CoeffPair p => (fderiv ℂ F t) (1,0)) univ := by
    exact ev.comp_analyticOnNhd hF.fderiv
  have heq : (fun t : ℂ × CoeffPair p =>
      deriv (canonicalDiscriminant hp (periodOnePotential t.2)) t.1) =
      (fun t : ℂ × CoeffPair p => (fderiv ℂ F t) (1,0)) := by
    funext t
    exact NLS.ComplexAnalysis.deriv_spectral_section_eq_fderiv F t.1 t.2
      ((hF t (mem_univ t)).differentiableAt)
  rw [heq]
  exact hderiv

/-- The actual quotient is jointly analytic on one open, connected
source neighborhood of the entire real-type locus, wherever the
spectral parameter avoids all moving gap segments. -/
theorem exists_global_sourceCriticalRootRatio_jointAnalytic
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ IsConnected W ∧
      realTypeSourceLocus p ⊆ W ∧
      IsOpen (sourceCanonicalRootJointDomain hp hp1 W) ∧
      AnalyticOnNhd ℂ (sourceCriticalRootRatioJoint hp hp1)
        (sourceCanonicalRootJointDomain hp hp1 W) := by
  obtain ⟨W, hWopen, hWconn, hreal, hDopen, hroot⟩ :=
    exists_global_source_analytic_canonicalRoot hp hp1
  refine ⟨W, hWopen, hWconn, hreal, hDopen, ?_⟩
  have hnum := (analyticOnNhd_sourceDiscriminantDerivative_joint hp hp1).mono
    (subset_univ (sourceCanonicalRootJointDomain hp hp1 W))
  intro t ht
  exact (hnum t ht).div (hroot t ht)
    (sourceCanonicalRoot_ne_zero_off_gaps hp hp1 t.2 t.1 ht.2)

/-- Near a real-type source, the same enclosing circle works for all
nearby complex sources, and the quotient at each point of that circle
is analytic in the source parameter. -/
theorem exists_local_sourceCriticalRootRatio_analyticOnEnclosingCircle
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (n : ℤ) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧
        (∀ ψ ∈ V,
          sourcePeriodicSegment hp hp1 ψ n ⊆ ball c R ∧
          closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n ∧
          sphere c R ⊆ sourceCanonicalRootDomain hp hp1 ψ) ∧
        (∀ z ∈ sphere c R,
          AnalyticOnNhd ℂ
            (fun ψ : CoeffPair p => sourceCriticalRootRatioJoint hp hp1 (z,ψ)) V) := by
  obtain ⟨W, hWopen, _, hreal, _, hquot⟩ :=
    exists_global_sourceCriticalRootRatio_jointAnalytic hp hp1
  obtain ⟨V₀, hV₀open, hφV₀, c, R, hR, hgeom⟩ :=
    exists_local_sourceCriticalRootRatio_uniformEnclosingCircle hp hp1 φ hφ n
  refine ⟨V₀ ∩ W, hV₀open.inter hWopen, ⟨hφV₀, hreal hφ⟩,
    c, R, hR, ?_, ?_⟩
  · intro ψ hψ
    exact hgeom ψ hψ.1
  · intro z hz ψ hψ
    have hpoint : (z,ψ) ∈ sourceCanonicalRootJointDomain hp hp1 W :=
      ⟨hψ.2, (hgeom ψ hψ.1).2.2 hz⟩
    exact (hquot (z,ψ) hpoint).comp
      (f := fun χ : CoeffPair p => (z,χ))
      (analyticAt_const.prod analyticAt_id)

end NLS.ZakharovShabat
