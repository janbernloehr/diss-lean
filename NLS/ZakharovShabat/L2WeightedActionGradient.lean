import NLS.ZakharovShabat.L2WholeLineDiscriminantGradient
import NLS.ZakharovShabat.L2GradientCurves
import NLS.ZakharovShabat.L2SourceGradientUniqueness
import NLS.ZakharovShabat.SourceHigherActionComplexGradient
import NLS.ComplexAnalysis.BilinearCircleIntegral

/-! # Genuine continuous physical gradients of weighted action contours

The contour is integrated in the Banach space of continuous physical curves.
Every original Hilbert direction pairs with this contour through a bounded
linear map, so no interchange of a rough pointwise double integral is assumed.
-/
noncomputable section
open Set Metric Complex MeasureTheory NLS.LinearVolterra NLS.ComplexAnalysis
namespace NLS.ZakharovShabat

def sourceWeightedGradientIntegrand (φ : CoeffPair 2) (w : ℂ → ℂ) (z : ℂ) : Curve (ℂ × ℂ) :=
  (w z*(sourceCanonicalRoot (by simp) (by norm_num) φ z)⁻¹) •
    l2DiscriminantGradientCurve (sourcePhysicalL2 φ) z

theorem circleIntegrable_sourceWeightedGradientIntegrand (φ : CoeffPair 2) (w : ℂ → ℂ)
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (hw : ContinuousOn w (sphere c r))
    (hc : sphere c r ⊆ sourceCanonicalRootDomain (by simp) (by norm_num) φ) :
    CircleIntegrable (sourceWeightedGradientIntegrand φ w) c r := by
  have hroot := (sourceCanonicalRoot_analyticOnNhd (by simp) (by norm_num) φ).continuousOn.mono hc
  exact ((hw.mul (hroot.inv₀ (fun z hz => sourceCanonicalRoot_ne_zero_off_gaps
    (by simp) (by norm_num) φ z (hc hz)))).smul
      (continuous_l2DiscriminantGradientCurve_spectral (sourcePhysicalL2 φ)).continuousOn).circleIntegrable hr

def sourceWeightedPhysicalGradientCurve (φ : CoeffPair 2) (w : ℂ → ℂ) (c : ℂ) (r : ℝ) :
    Curve (ℂ × ℂ) := -(Real.pi:ℂ)⁻¹ • ∮ z in C(c,r), sourceWeightedGradientIntegrand φ w z

theorem sourceWeightedPhysicalGradientCurve_pairing (φ h : CoeffPair 2) (w : ℂ → ℂ)
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (hw : ContinuousOn w (sphere c r))
    (hc : sphere c r ⊆ sourceCanonicalRootDomain (by simp) (by norm_num) φ) :
    l2GradientPairing (sourcePhysicalL2 h) (sourceWeightedPhysicalGradientCurve φ w c r) =
      -(Real.pi:ℂ)⁻¹ * ∮ z in C(c,r),
        w z*((sourceCanonicalRoot (by simp) (by norm_num) φ z)⁻¹*
          sourceDiscriminantCotangent (by simp) z φ h) := by
  rw [sourceWeightedPhysicalGradientCurve,map_smul,
    map_circleIntegral (l2GradientPairing (sourcePhysicalL2 h))
      (circleIntegrable_sourceWeightedGradientIntegrand φ w c r hr hw hc)]
  simp only [smul_eq_mul]
  congr 1
  apply circleIntegral.integral_congr hr
  intro z _
  dsimp only
  rw [sourceWeightedGradientIntegrand,map_smul,l2GradientPairing_discriminant,
    ← sourceDiscriminantCotangent_apply_eq_l2]
  simp only [smul_eq_mul]
  ring

theorem sourceWeightedPhysicalGradientCurve_apply (φ : CoeffPair 2) (w : ℂ → ℂ)
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (hw : ContinuousOn w (sphere c r))
    (hc : sphere c r ⊆ sourceCanonicalRootDomain (by simp) (by norm_num) φ)
    (s : Icc (0:ℝ) 1) :
    sourceWeightedPhysicalGradientCurve φ w c r s = -(Real.pi:ℂ)⁻¹ •
      ∮ z in C(c,r), (w z*(sourceCanonicalRoot (by simp) (by norm_num) φ z)⁻¹) •
        l2DiscriminantGradient (sourcePhysicalL2 φ) z s := by
  have hm := map_circleIntegral (ContinuousMap.evalCLM ℂ s : Curve (ℂ × ℂ) →L[ℂ] ℂ × ℂ)
    (circleIntegrable_sourceWeightedGradientIntegrand φ w c r hr hw hc)
  simpa only [sourceWeightedPhysicalGradientCurve,ContinuousMap.smul_apply,
    sourceWeightedGradientIntegrand,ContinuousMap.evalCLM_apply,l2DiscriminantGradientCurve_apply] using
    congrArg (fun v : ℂ × ℂ => -(Real.pi:ℂ)⁻¹ • v) hm

theorem sourceWeightedPhysicalGradientCurve_endpoints (φ : CoeffPair 2) (w : ℂ → ℂ)
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (hw : ContinuousOn w (sphere c r))
    (hc : sphere c r ⊆ sourceCanonicalRootDomain (by simp) (by norm_num) φ) :
    sourceWeightedPhysicalGradientCurve φ w c r ⟨1,by norm_num⟩ =
      sourceWeightedPhysicalGradientCurve φ w c r ⟨0,by norm_num⟩ := by
  rw [sourceWeightedPhysicalGradientCurve_apply φ w c r hr hw hc,
    sourceWeightedPhysicalGradientCurve_apply φ w c r hr hw hc]
  congr 1
  apply circleIntegral.integral_congr hr
  intro z _
  dsimp only
  have hp := periodic_l2WholeLineDiscriminantGradient (sourcePhysicalL2 φ) z 0
  simp only [zero_add] at hp
  rw [l2WholeLineDiscriminantGradient_on_unit _ _ ⟨1,by norm_num⟩,
    l2WholeLineDiscriminantGradient_on_unit _ _ ⟨0,by norm_num⟩] at hp
  rw [hp]

/-- Select the unique continuous physical representative of the actual
indexed higher-action cotangent, rather than making a new action functional. -/
def sourceHigherActionPhysicalGradientCurve (φ : CoeffPair 2) (n : ℤ) (k : ℕ) : Curve (ℂ × ℂ) :=
  sourcePhysicalGradientCurve (fderiv ℂ (sourceIndexedHigherAction (by simp) (by norm_num) n k) φ)

theorem exists_sourceHigherActionPhysicalGradients :
    ∃ U : Set (CoeffPair 2), IsOpen U ∧ realTypeSourceLocus 2 ⊆ U ∧
      ∀ φ ∈ U, ∀ n : ℤ, ∃ c : ℂ, ∃ r : ℝ, 0 < r ∧
        sphere c r ⊆ sourceCanonicalRootDomain (by simp) (by norm_num) φ ∧
        ∀ k : ℕ, SourcePhysicalGradientRepresents
          (fderiv ℂ (sourceIndexedHigherAction (by simp) (by norm_num) n k) φ)
          (sourceHigherActionPhysicalGradientCurve φ n k) ∧
          sourceHigherActionPhysicalGradientCurve φ n k =
            sourceWeightedPhysicalGradientCurve φ (fun z => z^k) c r := by
  obtain ⟨U,hU,hr,H⟩ := exists_sourceIndexedHigherAction_complex_gradients
    (p := 2) (by simp) (by norm_num)
  refine ⟨U,hU,hr,?_⟩
  intro φ hφ n
  obtain ⟨c,r,hr,hc,Hg⟩ := H φ hφ n
  refine ⟨c,r,hr,hc,?_⟩
  intro k
  have hg : SourcePhysicalGradientRepresents
      (fderiv ℂ (sourceIndexedHigherAction (by simp) (by norm_num) n k) φ)
      (sourceWeightedPhysicalGradientCurve φ (fun z => z^k) c r) := by
    intro h
    rw [← sourcePhysicalL2_gradient_pairing h,← l2GradientPairing_apply,
      sourceWeightedPhysicalGradientCurve_pairing φ h (fun z => z^k) c r hr.le
        (show ContinuousOn (fun z : ℂ => z^k) (sphere c r) from by fun_prop) hc]
    exact (Hg k).2 h
  have he : sourceHigherActionPhysicalGradientCurve φ n k =
      sourceWeightedPhysicalGradientCurve φ (fun z => z^k) c r := sourcePhysicalGradientCurve_eq_of_represents hg
  refine ⟨?_,he⟩
  rw [he]
  exact hg

theorem exists_sourceHigherActionPhysicalGradient_periodic_trace :
    ∃ U : Set (CoeffPair 2), IsOpen U ∧ realTypeSourceLocus 2 ⊆ U ∧
      ∀ φ ∈ U, ∀ n : ℤ, ∀ k : ℕ,
        sourceHigherActionPhysicalGradientCurve φ n k ⟨1,by norm_num⟩ =
          sourceHigherActionPhysicalGradientCurve φ n k ⟨0,by norm_num⟩ := by
  obtain ⟨U,hU,hr,H⟩ := exists_sourceHigherActionPhysicalGradients
  refine ⟨U,hU,hr,?_⟩
  intro φ hφ n k
  obtain ⟨c,r,hr,hc,Hg⟩ := H φ hφ n
  rw [(Hg k).2]
  exact sourceWeightedPhysicalGradientCurve_endpoints φ _ c r hr.le (by fun_prop) hc

end NLS.ZakharovShabat
