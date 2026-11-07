import NLS.KdV.PseudomeasureComplexRiesz

/-!
# Actual algebraic counting for complex singular Hill potentials

Inside any physical resolvent circle, the actual count is the sum of full
original root-space dimensions. It equals the rank of the actual projection
and is invariant along preconnected continuous complex potential families
with that common circle. The native theorem assumes a physical resolvent
circle; uniform circle existence is established separately on the article's
original complex norm balls. No spectral count is assumed.
-/
noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

/-- Every disk contains only finitely many actual original complex spectral points. -/
theorem finite_endpointHillSpectrum_in_ball (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (c : ℂ) (ρ : ℝ) :
    Set.Finite {z : ℂ | z ∈ endpointHillSpectrum r hr1 q ∧ z ∈ ball c ρ} := by
  apply (finite_endpointHillSpectrum_norm_le r hr hr1 q (‖c‖+ρ)).subset
  rintro z ⟨hz, hb⟩
  refine ⟨hz, ?_⟩
  have hdist : ‖z-c‖ < ρ := by simpa only [mem_ball, dist_eq_norm] using hb
  have hn : ‖z‖ ≤ ‖z-c‖+‖c‖ := by
    simpa only [sub_add_cancel] using norm_add_le (z-c) c
  linarith

/-- The actual finite enclosed spectrum; there is no reality restriction. -/
def endpointHillEnclosedSpectrum (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (c : ℂ) (ρ : ℝ) : Finset ℂ :=
  (finite_endpointHillSpectrum_in_ball r hr hr1 q c ρ).toFinset

/-- Enclosed spectral points are exactly the actual spectral points inside the disk. -/
theorem mem_endpointHillEnclosedSpectrum (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (c : ℂ) (ρ : ℝ) (z : ℂ) :
    z ∈ endpointHillEnclosedSpectrum r hr hr1 q c ρ ↔
      z ∈ endpointHillSpectrum r hr1 q ∧ z ∈ ball c ρ := by
  simp only [endpointHillEnclosedSpectrum, Set.Finite.mem_toFinset, mem_ofPred_eq]

/-- The sum of ACTUAL full physical algebraic multiplicities enclosed by the circle. -/
def endpointHillEnclosedAlgebraicCount (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (c : ℂ) (ρ : ℝ) : ℕ :=
  ∑ z ∈ endpointHillEnclosedSpectrum r hr hr1 q c ρ,
    endpointHillAlgebraicMultiplicity r hr hr1 q z

/-- The actual Riesz range is the sum over the actual finite enclosed complex spectrum. -/
theorem endpointHillRieszProjection_range_eq_enclosed_roots (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
    (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hc : sphere c ρ ⊆ endpointHillResolventSet r hr1 q) :
    (endpointHillRieszProjection r hr1 q c ρ).range =
      ⨆ z : endpointHillEnclosedSpectrum r hr hr1 q c ρ,
        singularHillRootSpaceTop (endpointHillHminusOne SpectralWeight.one r hr1 q) z.val := by
  obtain ⟨a, ha⟩ := endpointHillResolventSet_nonempty r hr hr1 q
  rw [endpointHillRieszProjection_range_eq_roots_complex r hr1 q c ρ hρ hc a ha]
  apply le_antisymm
  · apply iSup_le
    intro z
    by_cases hz : z.val ∈ endpointHillSpectrum r hr1 q
    · exact le_iSup_of_le ⟨z.val, (mem_endpointHillEnclosedSpectrum r hr hr1 q c ρ z.val).mpr
        ⟨hz, z.property⟩⟩ le_rfl
    · have hres : z.val ∈ endpointHillResolventSet r hr1 q := by
        simpa only [endpointHillSpectrum, mem_compl_iff, not_not] using hz
      rw [endpointHillRootSpaceTop_eq_bot_of_mem_resolvent r hr1 q z.val hres]
      exact bot_le
  · apply iSup_le
    intro z
    exact le_iSup_of_le ⟨z.val,
      ((mem_endpointHillEnclosedSpectrum r hr hr1 q c ρ z.val).mp z.property).2⟩ le_rfl

/-- Projection rank equals the actual enclosed algebraic count for every complex potential. -/
theorem endpointHillRieszProjection_rank_eq_algebraicCount (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
    (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hc : sphere c ρ ⊆ endpointHillResolventSet r hr1 q) :
    Module.finrank ℂ (endpointHillRieszProjection r hr1 q c ρ).range =
      endpointHillEnclosedAlgebraicCount r hr hr1 q c ρ := by
  obtain ⟨a, ha⟩ := endpointHillResolventSet_nonempty r hr hr1 q
  let V := fun z : endpointHillEnclosedSpectrum r hr hr1 q c ρ =>
    singularHillRootSpaceTop (endpointHillHminusOne SpectralWeight.one r hr1 q) z.val
  let (z : endpointHillEnclosedSpectrum r hr hr1 q c ρ) : FiniteDimensional ℂ (V z) :=
    finiteDimensional_endpointHillRootSpaceTop r hr hr1 q z.val
  have hind : iSupIndep V :=
    (independent_endpointHillRootSpaceTop r hr1 q a ha).comp Subtype.val_injective
  have he := NLS.FunctionalAnalysis.finrank_iSup_of_iSupIndep V hind
  rw [← endpointHillRieszProjection_range_eq_enclosed_roots r hr hr1 q c ρ hρ hc] at he
  change Module.finrank ℂ (endpointHillRieszProjection r hr1 q c ρ).range =
    ∑ z : endpointHillEnclosedSpectrum r hr hr1 q c ρ,
      endpointHillAlgebraicMultiplicity r hr hr1 q z.val at he
  simpa only [endpointHillEnclosedAlgebraicCount, Finset.sum_coe_sort] using he

/-- The ACTUAL enclosed algebraic count is invariant along preconnected complex
potential families with a common physical resolvent circle. -/
theorem endpointHillEnclosedAlgebraicCount_eq_on_preconnected (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    {X : Type*} [TopologicalSpace X]
    (q : X → WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
    (s : Set X) (hs : IsPreconnected s) (hq : ContinuousOn q s)
    (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hc : ∀ x ∈ s, sphere c ρ ⊆ endpointHillResolventSet r hr1 (q x))
    {a b : X} (ha : a ∈ s) (hb : b ∈ s) :
    endpointHillEnclosedAlgebraicCount r hr hr1 (q a) c ρ =
      endpointHillEnclosedAlgebraicCount r hr hr1 (q b) c ρ := by
  rw [← endpointHillRieszProjection_rank_eq_algebraicCount r hr hr1 (q a) c ρ hρ (hc a ha),
    ← endpointHillRieszProjection_rank_eq_algebraicCount r hr hr1 (q b) c ρ hρ (hc b hb)]
  exact endpointHillRieszProjection_rank_eq r hr1 q s hs hq c ρ hρ hc ha hb

end NLS.KdV
