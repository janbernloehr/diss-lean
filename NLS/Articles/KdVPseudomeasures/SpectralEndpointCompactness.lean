import NLS.Articles.KdVPseudomeasures.SpectralEndpointBootstrap
import NLS.Articles.KdVPseudomeasures.SourceWeakStarCompactSets

/-! Endpoint compactness through Appendix B, preserving entire original
smooth-test distributions. The lower compact realization is an explicit
hypothesis; no inverse spectral compactness theorem is assumed implicitly. -/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue

/-- All target-order physical representatives of exactly the supplied original family. -/
def sourceReinterpretationSet (r t : ℝ) (A : Set (Potential r)) : Set (WeakStarPotential t) :=
  {p | ∃ q ∈ A, p.toPotential.val.val = q.val.val}

/-- Appendix B transfers a compact lower realization once uniform target
regularity has been proved. Equality is of entire distributions, not only spectra. -/
theorem isCompact_sourceReinterpretationSet_of_lower_compact (r t σ : ℝ)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (h : 1 < (-t-σ)*p.toReal)
    (A : Set (Potential r))
    (hreg : ∃ C : ℝ, ∀ q ∈ A, ∃ v : Potential t, v.val.val = q.val.val ∧ ‖v.val‖ ≤ C)
    (K : Set (FourierLebesgueSpace (2:ℝ) σ p)) (hK : IsCompact K)
    (hvalues : (fun u : FourierLebesgueSpace (2:ℝ) σ p => u.val) '' K =
      (fun q : Potential r => q.val.val) '' A) :
    IsCompact (sourceReinterpretationSet r t A) := by
  obtain ⟨C, hC⟩ := hreg
  have hb : PotentialNormBounded t (sourceReinterpretationSet r t A) := by
    refine ⟨C, ?_⟩
    rintro v ⟨q, hq, hv⟩
    obtain ⟨u, hu, hun⟩ := hC q hq
    have he : v.toPotential.val = u.val := Subtype.ext (hv.trans hu.symm)
    simpa only [he] using hun
  apply (isCompact_source_iff_bounded_lower_compact t σ hp h _).mpr
  refine ⟨hb, ?_⟩
  have he : sourceLowerDistribution t σ hp h '' sourceReinterpretationSet r t A = K := by
    ext u
    constructor
    · rintro ⟨v, ⟨q, hq, hv⟩, rfl⟩
      have hm : q.val.val ∈ (fun q : Potential r => q.val.val) '' A := ⟨q, hq, rfl⟩
      rw [← hvalues] at hm
      obtain ⟨z, hz, hez⟩ := hm
      have he : sourceLowerDistribution t σ hp h v = z := by
        apply Subtype.ext
        rw [sourceLowerDistribution_val]
        exact hv.trans hez.symm
      exact he.symm ▸ hz
    · intro hu
      have hm : u.val ∈ (fun u : FourierLebesgueSpace (2:ℝ) σ p => u.val) '' K := ⟨u, hu, rfl⟩
      rw [hvalues] at hm
      obtain ⟨q, hq, hqu⟩ := hm
      obtain ⟨v, hv, _⟩ := hC q hq
      refine ⟨⟨v⟩, ⟨q, hq, hv⟩, ?_⟩
      apply Subtype.ext
      rw [sourceLowerDistribution_val]
      exact hv.trans hqu
  exact he ▸ hK

/-- A compact finite-p realization bounds the original base endpoint norm,
provided its entire distribution range is the supplied family. -/
theorem source_normBounded_of_compact_finite_realization (r : ℝ)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (A : Set (Potential r))
    (K : Set (FourierLebesgueSpace (2:ℝ) (-r) p)) (hK : IsCompact K)
    (hvalues : (fun u : FourierLebesgueSpace (2:ℝ) (-r) p => u.val) '' K =
      (fun q : Potential r => q.val.val) '' A) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ q ∈ A, ‖q.val‖ ≤ R := by
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hK.isBounded
  refine ⟨max R 0, le_max_right _ _, fun q hq => ?_⟩
  have hm : q.val.val ∈ (fun q : Potential r => q.val.val) '' A := ⟨q, hq, rfl⟩
  rw [← hvalues] at hm
  obtain ⟨u, hu, he⟩ := hm
  obtain ⟨v, hv, hvn⟩ := exists_of_endpoint_bound (Weight.sobolev (-r)) q.val.val
    (max R 0) (le_max_right _ _) (fun k => by
      rw [← he]
      exact (weight_mul_norm_coefficient_le (Weight.sobolev (-r)) p u k).trans
        ((hR u hu).trans (le_max_left _ _)))
  have heq : q.val = v := Subtype.ext hv.symm
  simpa only [heq] using hvn

/-- Actual canonical stronger gap bounds and a compact original finite-p
realization give weak-star compactness at the stronger endpoint order.
The finite-p compactness input remains explicit and must be established
separately for an actual isospectral set. -/
theorem isCompact_sourceReinterpretationSet_of_gap_bound (r : ℝ)
    (hr : AdmissiblePredualOrder r) (t : ℝ) (ht : 0 ≤ t) (htr : t ≤ r)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (h : 1 < (r-t)*p.toReal)
    (A : Set (Potential r)) (G : ℝ) (hG : 0 ≤ G)
    (hgap : ∀ q ∈ A, ∀ n : ℕ, 1 ≤ n →
      Weight.sobolev (-t) (n:ℤ)*‖sourceCanonicalGapValues r hr q (n:ℤ)‖ ≤ G)
    (K : Set (FourierLebesgueSpace (2:ℝ) (-r) p)) (hK : IsCompact K)
    (hvalues : (fun u : FourierLebesgueSpace (2:ℝ) (-r) p => u.val) '' K =
      (fun q : Potential r => q.val.val) '' A) :
    (∀ q ∈ A, ∃ v : Potential t, v.val.val = q.val.val) ∧
      IsCompact (sourceReinterpretationSet r t A) := by
  obtain ⟨R, hR, hb⟩ := source_normBounded_of_compact_finite_realization r A K hK hvalues
  obtain ⟨C, _, hC⟩ := source_uniform_endpoint_bootstrap r hr t ht htr R G hR hG
  have hreg : ∀ q ∈ A, ∃ v : Potential t, v.val.val = q.val.val ∧ ‖v.val‖ ≤ C :=
    fun q hq => hC q (hb q hq) (hgap q hq)
  refine ⟨fun q hq => ?_, isCompact_sourceReinterpretationSet_of_lower_compact
    r t (-r) hp (by convert h using 1; ring) A ⟨C, hreg⟩ K hK hvalues⟩
  obtain ⟨v, hv, _⟩ := hreg q hq
  exact ⟨v, hv⟩

end NLS.Articles.KdVPseudomeasures
