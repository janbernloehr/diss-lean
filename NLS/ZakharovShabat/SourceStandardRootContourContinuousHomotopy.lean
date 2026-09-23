import NLS.ComplexAnalysis.ContinuousSmoothLoopHomotopy
import NLS.ZakharovShabat.SourceStandardRootContourLocalStability
import NLS.ZakharovShabat.SourceStandardRootContourConvexIndexed

/-!
# Standard-root integrals along continuous families of smooth loops

A continuous homotopy with twice-smooth closed slices preserves the
inverse-root integral when every slice avoids the indexed gap. No
twice-smoothness of the map on the full homotopy square is required.
Moving basepoints are allowed. Combined with the arbitrary-loop
off-diagonal theorem, this yields the indexed contour identity.
-/

noncomputable section
open Set Metric Complex
open scoped unitInterval ENNReal
namespace NLS.ZakharovShabat

/-- Inverse-root curve integrals agree along continuous homotopies with
twice-smooth closed slices avoiding the indexed gap. -/
theorem sourceStandardRoot_inv_curveIntegral_eq_of_continuous_smooth_homotopy
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ)
    {a b : ℂ} {γ₁ : Path a a} {γ₂ : Path b b}
    (H : (γ₁ : C(I, ℂ)).Homotopy γ₂)
    (hloop : ∀ s : I, H (s, 1) = H (s, 0))
    (hsmooth : ∀ s : I,
      ContDiffOn ℝ 2 (NLS.ComplexAnalysis.homotopyLoop H hloop s).extend (Icc 0 1))
    (havoid : ∀ s u : I, H (s,u) ∉ sourcePeriodicSegment hp hp1 ψ n) :
    (∫ᶜ z in γ₁, NLS.ComplexAnalysis.holomorphicOneForm
      (fun w => (sourceStandardRoot hp hp1 ψ n w)⁻¹) z) =
    ∫ᶜ z in γ₂, NLS.ComplexAnalysis.holomorphicOneForm
      (fun w => (sourceStandardRoot hp hp1 ψ n w)⁻¹) z := by
  refine NLS.ComplexAnalysis.curveIntegral_eq_of_continuous_smooth_loop_homotopy
    (fun w => (sourceStandardRoot hp hp1 ψ n w)⁻¹)
    (sourcePeriodicSegment hp hp1 ψ n)ᶜ ?_ ?_ H hloop hsmooth ?_
  · exact (isClosed_sourcePeriodicSegment hp hp1 ψ n).isOpen_compl
  · intro z hz
    exact (sourceStandardRoot_inv_analyticAt hp hp1 ψ n z hz).differentiableAt
  · exact havoid

/-- A continuous homotopy from an enclosing circle through smooth
gap-avoiding loops gives the normalized diagonal value `−1`. -/
theorem normalized_sourceStandardRoot_inv_curveIntegral_of_continuous_smooth_homotopy_circle
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ)
    (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hseg : sourcePeriodicSegment hp hp1 ψ n ⊆ ball c r)
    {a : ℂ} {γ : Path a a}
    (H : (NLS.ComplexAnalysis.circlePath c r : C(I, ℂ)).Homotopy γ)
    (hloop : ∀ s : I, H (s, 1) = H (s, 0))
    (hsmooth : ∀ s : I,
      ContDiffOn ℝ 2 (NLS.ComplexAnalysis.homotopyLoop H hloop s).extend (Icc 0 1))
    (havoid : ∀ s u : I, H (s,u) ∉ sourcePeriodicSegment hp hp1 ψ n) :
    (2*Real.pi*Complex.I)⁻¹ *
      (∫ᶜ z in γ, NLS.ComplexAnalysis.holomorphicOneForm
        (fun w => (sourceStandardRoot hp hp1 ψ n w)⁻¹) z) = -1 := by
  have heq := sourceStandardRoot_inv_curveIntegral_eq_of_continuous_smooth_homotopy
    hp hp1 ψ n H hloop hsmooth havoid
  have hnonzero : (2*Real.pi*Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero]
  calc
    (2*Real.pi*Complex.I)⁻¹ *
        (∫ᶜ z in γ, NLS.ComplexAnalysis.holomorphicOneForm
          (fun w => (sourceStandardRoot hp hp1 ψ n w)⁻¹) z) =
      (2*Real.pi*Complex.I)⁻¹ *
        (∫ᶜ z in NLS.ComplexAnalysis.circlePath c r,
          NLS.ComplexAnalysis.holomorphicOneForm
            (fun w => (sourceStandardRoot hp hp1 ψ n w)⁻¹) z) := by rw [heq]
    _ = (2*Real.pi*Complex.I)⁻¹ * -(2*Real.pi*Complex.I) := by
      rw [NLS.ComplexAnalysis.curveIntegral_circlePath,
        circleIntegral_sourceStandardRoot_inv_of_gap_mem_ball hp hp1 ψ n c r hr hseg]
    _ = -1 := by
      calc
        (2*Real.pi*Complex.I)⁻¹ * -(2*Real.pi*Complex.I) =
          -((2*Real.pi*Complex.I)⁻¹ * (2*Real.pi*Complex.I)) := by ring
        _ = -1 := by rw [inv_mul_cancel₀ hnonzero]

/-- The indexed inverse-root identity for an isolating-disc loop with a
continuous, slice-wise smooth gap-avoiding homotopy from an enclosing
circle. The off-diagonal case needs only the target loop in the disc. -/
theorem normalized_sourceStandardRoot_inv_curveIntegral_indexed_of_continuous_smooth_homotopy
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ ψ : CoeffPair p)
    (N : ℕ) (ε : ℝ) (m n : ℤ)
    (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hsegm : sourcePeriodicSegment hp hp1 ψ m ⊆ ball c r)
    (hcluster : sourceSpectralCluster hp hp1 ψ n ⊆
      sourceIsolatingDisc hp hp1 φ N ε n)
    (hdisjoint : m ≠ n → Disjoint
      (sourceIsolatingDisc hp hp1 φ N ε m)
      (sourceIsolatingDisc hp hp1 φ N ε n))
    {a : ℂ} (γ : Path a a)
    (hγ : ContDiffOn ℝ 2 γ.extend (Icc 0 1))
    (hγinside : ∀ u : I, γ u ∈ sourceIsolatingDisc hp hp1 φ N ε m)
    (H : (NLS.ComplexAnalysis.circlePath c r : C(I, ℂ)).Homotopy γ)
    (hloop : ∀ s : I, H (s, 1) = H (s, 0))
    (hsmooth : ∀ s : I,
      ContDiffOn ℝ 2 (NLS.ComplexAnalysis.homotopyLoop H hloop s).extend (Icc 0 1))
    (havoidm : ∀ s u : I, H (s,u) ∉ sourcePeriodicSegment hp hp1 ψ m) :
    (2*Real.pi*Complex.I)⁻¹ *
      (∫ᶜ z in γ, NLS.ComplexAnalysis.holomorphicOneForm
        (fun w => (sourceStandardRoot hp hp1 ψ n w)⁻¹) z) =
      if m = n then -1 else 0 := by
  by_cases hmn : m = n
  · subst n
    simpa using normalized_sourceStandardRoot_inv_curveIntegral_of_continuous_smooth_homotopy_circle
      hp hp1 ψ m c r hr hsegm H hloop hsmooth havoidm
  · have hzero := sourceStandardRoot_inv_curveIntegral_off_index_eq_zero
      hp hp1 φ ψ N ε m n hcluster (hdisjoint hmn) γ hγ hγinside
    rw [hzero]
    simp [hmn]

end NLS.ZakharovShabat
