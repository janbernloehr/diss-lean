import NLS.ComplexAnalysis.CircleCurveIntegral
import NLS.ZakharovShabat.SourceStandardRootContourHomotopy

/-!
# The inverse standard-root integral on smoothly deformable contours

A smooth closed loop joined to an enclosing circle by a gap-avoiding
smooth homotopy has reciprocal-root integral `−2πi`, hence normalized
value `−1`. The circle-path bridge identifies Mathlib's curve and circle
integrals with the same orientation.
-/

noncomputable section
open Set
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat

/-- A smooth counterclockwise loop homotopic away from the gap to an
 enclosing circle has reciprocal-root integral `−2πi`. -/
theorem sourceStandardRoot_inv_curveIntegral_of_homotopy_circle
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ)
    (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hseg : sourcePeriodicSegment hp hp1 ψ n ⊆ Metric.ball c r)
    {a : ℂ} {γ : Path a a}
    (φ : (NLS.ComplexAnalysis.circlePath c r : C(I, ℂ)).Homotopy γ)
    (hloop : ∀ s : I, φ (s, 1) = φ (s, 0))
    {t : Set ℂ}
    (hφt : ∀ s ∈ Ioo (0:I) 1, ∀ u ∈ Ioo (0:I) 1, φ (s, u) ∈ t)
    (havoid : closure t ⊆ (sourcePeriodicSegment hp hp1 ψ n)ᶜ)
    (hcontdiff : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ ↦ Set.IccExtend zero_le_one (φ.extend xy.1) xy.2) (Icc 0 1)) :
    ∫ᶜ z in γ, NLS.ComplexAnalysis.holomorphicOneForm
      (fun w => (sourceStandardRoot hp hp1 ψ n w)⁻¹) z =
        -(2*Real.pi*Complex.I) := by
  let f : ℂ → ℂ := fun w => (sourceStandardRoot hp hp1 ψ n w)⁻¹
  calc
    ∫ᶜ z in γ, NLS.ComplexAnalysis.holomorphicOneForm f z =
        ∫ᶜ z in NLS.ComplexAnalysis.circlePath c r,
          NLS.ComplexAnalysis.holomorphicOneForm f z :=
      (sourceStandardRoot_inv_curveIntegral_eq_of_homotopy
        hp hp1 ψ n φ hloop hφt havoid hcontdiff).symm
    _ = ∮ z in C(c, r), f z :=
      NLS.ComplexAnalysis.curveIntegral_circlePath f c r
    _ = -(2*Real.pi*Complex.I) :=
      circleIntegral_sourceStandardRoot_inv_of_gap_mem_ball
        hp hp1 ψ n c r hr hseg

/-- The normalized inverse-root integral equals `−1` on each
smooth loop homotopic to an enclosing circle away from the gap. -/
theorem normalized_sourceStandardRoot_inv_curveIntegral_of_homotopy_circle
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ)
    (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hseg : sourcePeriodicSegment hp hp1 ψ n ⊆ Metric.ball c r)
    {a : ℂ} {γ : Path a a}
    (φ : (NLS.ComplexAnalysis.circlePath c r : C(I, ℂ)).Homotopy γ)
    (hloop : ∀ s : I, φ (s, 1) = φ (s, 0))
    {t : Set ℂ}
    (hφt : ∀ s ∈ Ioo (0:I) 1, ∀ u ∈ Ioo (0:I) 1, φ (s, u) ∈ t)
    (havoid : closure t ⊆ (sourcePeriodicSegment hp hp1 ψ n)ᶜ)
    (hcontdiff : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ ↦ Set.IccExtend zero_le_one (φ.extend xy.1) xy.2) (Icc 0 1)) :
    (2*Real.pi*Complex.I)⁻¹ *
      (∫ᶜ z in γ, NLS.ComplexAnalysis.holomorphicOneForm
        (fun w => (sourceStandardRoot hp hp1 ψ n w)⁻¹) z) = -1 := by
  rw [sourceStandardRoot_inv_curveIntegral_of_homotopy_circle
    hp hp1 ψ n c r hr hseg φ hloop hφt havoid hcontdiff]
  have hnonzero : (2*Real.pi*Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero]
  calc
    (2*Real.pi*Complex.I)⁻¹ * -(2*Real.pi*Complex.I) =
        -((2*Real.pi*Complex.I)⁻¹ * (2*Real.pi*Complex.I)) := by ring
    _ = -1 := by rw [inv_mul_cancel₀ hnonzero]

end NLS.ZakharovShabat
