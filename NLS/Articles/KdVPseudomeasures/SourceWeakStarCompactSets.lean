import NLS.Articles.KdVPseudomeasures.SourceWeakStarNets

/-!
# Compact sets and closed Fourier constraints in the original source space

These consequences of Appendix B use the exact original endpoint norm.
Relative compactness is characterized in the physical weak-star space;
closed lower-norm images require both endpoint boundedness and weak-star
closedness. No assertion is made that lower-norm boundedness suffices.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest
open NLS.Fourier.PeriodicFourierLebesgue

/-- Relative weak-star compactness is exactly original endpoint norm boundedness. -/
theorem isCompact_closure_source_iff_bounded (r : ℝ) (A : Set (WeakStarPotential r)) :
    IsCompact (closure A) ↔ PotentialNormBounded r A := by
  rw [isCompact_source_iff_bounded_closed, potentialNormBounded_closure_iff]
  exact and_iff_left isClosed_closure

/-- Relative sequential compactness has the same endpoint boundedness criterion. -/
theorem isSeqCompact_closure_source_iff_bounded (r : ℝ) (A : Set (WeakStarPotential r)) :
    IsSeqCompact (closure A) ↔ PotentialNormBounded r A := by
  rw [← isCompact_source_iff_isSeqCompact, isCompact_closure_source_iff_bounded]

/-- Each original Fourier coefficient is continuous on the entire weak-star space. -/
theorem continuous_sourceCoefficient (r : ℝ) (n : ℤ) :
    Continuous (fun q : WeakStarPotential r => q.toPotential.val.val (mode (-n))) := by
  have hc := (continuous_apply n).comp
    ((WeightedCoeff.continuous_weakStarCoordinates r).comp
      (isClosedEmbedding_weakStarPotentialCoordinates r).continuous)
  simpa only [Function.comp_def, weakStarPotentialCoordinates,
    potentialCoordinates_apply] using hc

/-- Arbitrarily many closed Fourier constraints form a weak-star closed physical set. -/
theorem isClosed_sourceCoefficientConstraints (r : ℝ) (C : ℤ → Set ℂ)
    (hC : ∀ n, IsClosed (C n)) :
    IsClosed {q : WeakStarPotential r | ∀ n, q.toPotential.val.val (mode (-n)) ∈ C n} := by
  have he : {q : WeakStarPotential r | ∀ n, q.toPotential.val.val (mode (-n)) ∈ C n} =
      ⋂ n : ℤ, (fun q : WeakStarPotential r => q.toPotential.val.val (mode (-n))) ⁻¹' C n := by
    ext q
    simp only [mem_ofPred_eq, mem_iInter, mem_preimage]
  rw [he]
  exact isClosed_iInter fun n => (hC n).preimage (continuous_sourceCoefficient r n)

/-- A specified original norm bound and any closed Fourier constraints give a compact set. -/
theorem isCompact_sourceNormBall_coefficientConstraints (r R : ℝ) (C : ℤ → Set ℂ)
    (hC : ∀ n, IsClosed (C n)) :
    IsCompact {q : WeakStarPotential r | ‖q.toPotential.val‖ ≤ R ∧
      ∀ n, q.toPotential.val.val (mode (-n)) ∈ C n} :=
  (isCompact_sourceNormBall r R).inter_right (isClosed_sourceCoefficientConstraints r C hC)

/-- Closed bounded physical sets embed as closed sets in every admissible lower norm space. -/
theorem isClosedEmbedding_sourceLowerDistribution_on_closed_bounded (r t : ℝ)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (h : 1 < (-r-t)*p.toReal)
    (A : Set (WeakStarPotential r)) (hb : PotentialNormBounded r A) (hc : IsClosed A) :
    Topology.IsClosedEmbedding (fun q : A => sourceLowerDistribution r t hp h q.val) := by
  let : CompactSpace A := isCompact_iff_compactSpace.mp
    ((isCompact_source_iff_bounded_closed r A).mpr ⟨hb, hc⟩)
  have he := isEmbedding_sourceLowerDistribution_on_bounded r t hp h A hb
  exact he.continuous.isClosedEmbedding he.injective

/-- The physical norm ball has a closed lower-norm image, with its weak-star topology retained. -/
theorem isClosedEmbedding_sourceLowerDistribution_on_normBall (r t R : ℝ)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (h : 1 < (-r-t)*p.toReal) :
    Topology.IsClosedEmbedding (fun q : {q : WeakStarPotential r | ‖q.toPotential.val‖ ≤ R} =>
      sourceLowerDistribution r t hp h q.val) :=
  isClosedEmbedding_sourceLowerDistribution_on_closed_bounded r t hp h _
    ⟨R, fun _ hq => hq⟩ (isClosed_sourceNormBall r R)

/-- Subsequence extraction preserves a specified bound and all closed Fourier constraints. -/
theorem exists_source_subseq_coefficientConstraints (r R : ℝ) (C : ℤ → Set ℂ)
    (hC : ∀ n, IsClosed (C n)) (x : ℕ → WeakStarPotential r)
    (hb : ∀ k, ‖(x k).toPotential.val‖ ≤ R)
    (hx : ∀ k n, (x k).toPotential.val.val (mode (-n)) ∈ C n) :
    ∃ a : WeakStarPotential r, ‖a.toPotential.val‖ ≤ R ∧
      (∀ n, a.toPotential.val.val (mode (-n)) ∈ C n) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a) ∧
        ∀ (t : ℝ) (p : ℝ≥0∞) (hp1 : 1 ≤ p) (hp : p ≠ ⊤)
          (h : 1 < (-r-t)*p.toReal),
          letI : Fact (1 ≤ p) := ⟨hp1⟩
          Tendsto (fun k => sourceLowerDistribution r t hp h (x (φ k))) atTop
            (𝓝 (sourceLowerDistribution r t hp h a)) := by
  obtain ⟨a, ha, φ, hφ, ht, hl⟩ := exists_source_subseq_all_lower_of_bounded r x
    ⟨R, by rintro _ ⟨k, rfl⟩; exact hb k⟩
  have hclosed : IsClosed {q : WeakStarPotential r | ‖q.toPotential.val‖ ≤ R ∧
      ∀ n, q.toPotential.val.val (mode (-n)) ∈ C n} :=
    (isClosed_sourceNormBall r R).inter (isClosed_sourceCoefficientConstraints r C hC)
  have ham := closure_minimal (fun q hq => by
    obtain ⟨k, rfl⟩ := hq
    exact ⟨hb k, hx k⟩) hclosed ha
  exact ⟨a, ham.1, ham.2, φ, hφ, ht, hl⟩

end NLS.Articles.KdVPseudomeasures
