import NLS.ComplexAnalysis.LocalHolomorphicLoopStability
import NLS.ZakharovShabat.SourceStandardRootContourHomotopy

/-!
# Local stability of inverse-root contour integrals

The closed periodic gap is a compact segment. A smooth loop avoiding it
has a uniform neighborhood of smooth loops with the same inverse-root
integral. In particular, a diagonal value of `−1` persists under every
sufficiently small uniform perturbation.
-/

noncomputable section
open Set Metric Complex
open scoped unitInterval ENNReal
namespace NLS.ZakharovShabat

/-- The closed periodic gap segment is a closed subset of the complex
plane. -/
theorem isClosed_sourcePeriodicSegment
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ) :
    IsClosed (sourcePeriodicSegment hp hp1 ψ n) := by
  have hcompact : IsCompact (sourcePeriodicSegment hp hp1 ψ n) := by
    unfold sourcePeriodicSegment
    rw [segment_eq_image_lineMap]
    exact isCompact_Icc.image AffineMap.lineMap_continuous
  exact hcompact.isClosed

/-- Every smooth loop avoiding the indexed gap has a positive uniform
perturbation radius on which its inverse-root integral is constant. -/
theorem exists_sourceStandardRoot_inv_curveIntegral_eq_of_uniform_perturbation
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ)
    {a : ℂ} (γ : Path a a)
    (hγ : ContDiffOn ℝ 2 γ.extend (Icc 0 1))
    (havoid : ∀ u : I, γ u ∉ sourcePeriodicSegment hp hp1 ψ n) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ {b : ℂ} (η : Path b b),
        ContDiffOn ℝ 2 η.extend (Icc 0 1) →
        (∀ u : I, dist (η u) (γ u) ≤ δ) →
        (∫ᶜ z in η, NLS.ComplexAnalysis.holomorphicOneForm
          (fun w => (sourceStandardRoot hp hp1 ψ n w)⁻¹) z) =
        ∫ᶜ z in γ, NLS.ComplexAnalysis.holomorphicOneForm
          (fun w => (sourceStandardRoot hp hp1 ψ n w)⁻¹) z := by
  apply NLS.ComplexAnalysis.exists_curveIntegral_eq_of_uniform_perturbation
    (fun w => (sourceStandardRoot hp hp1 ψ n w)⁻¹)
    (sourcePeriodicSegment hp hp1 ψ n)ᶜ
  · exact (isClosed_sourcePeriodicSegment hp hp1 ψ n).isOpen_compl
  · intro z hz
    exact (sourceStandardRoot_inv_analyticAt hp hp1 ψ n z hz).differentiableAt
  · exact hγ
  · intro u
    exact havoid u

/-- A normalized diagonal inverse-root value of `−1` persists for all
sufficiently close twice-smooth closed loops. -/
theorem exists_normalized_sourceStandardRoot_inv_eq_neg_one_of_uniform_perturbation
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ)
    {a : ℂ} (γ : Path a a)
    (hγ : ContDiffOn ℝ 2 γ.extend (Icc 0 1))
    (havoid : ∀ u : I, γ u ∉ sourcePeriodicSegment hp hp1 ψ n)
    (hvalue : (2*Real.pi*Complex.I)⁻¹ *
      (∫ᶜ z in γ, NLS.ComplexAnalysis.holomorphicOneForm
        (fun w => (sourceStandardRoot hp hp1 ψ n w)⁻¹) z) = -1) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ {b : ℂ} (η : Path b b),
        ContDiffOn ℝ 2 η.extend (Icc 0 1) →
        (∀ u : I, dist (η u) (γ u) ≤ δ) →
        (2*Real.pi*Complex.I)⁻¹ *
          (∫ᶜ z in η, NLS.ComplexAnalysis.holomorphicOneForm
            (fun w => (sourceStandardRoot hp hp1 ψ n w)⁻¹) z) = -1 := by
  obtain ⟨δ, hδ, heq⟩ :=
    exists_sourceStandardRoot_inv_curveIntegral_eq_of_uniform_perturbation
      hp hp1 ψ n γ hγ havoid
  refine ⟨δ, hδ, ?_⟩
  intro b η hη hclose
  rw [heq η hη hclose]
  exact hvalue

end NLS.ZakharovShabat
