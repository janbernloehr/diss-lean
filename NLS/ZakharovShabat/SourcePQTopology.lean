import NLS.ZakharovShabat.ResonantSeriesApproximation
import Mathlib.Topology.Algebra.Module.Complement

/-! # The literal closed Fourier spans in the P/Q decomposition

The resonant subspace is the span of the two individual signed modes.
The complementary subspace is the closure of the span of all other signed
modes. These are the actual projection ranges and topological complements
in the original weighted pair space for every finite Banach exponent.
-/

noncomputable section
open scoped ENNReal Classical
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- One of the two literal signed Fourier modes, with unit raw amplitude. -/
def sourceSignedFourierMode (w : Weight) (k : ℤ) (i : Fin 2) : WeightedCoeffPair w p :=
  resonantSynthesis w k (Pi.single i 1)

/-- The algebraic span of the individual signed modes with source index different from n. -/
def sourceNonresonantModeSpan (w : Weight) (n : ℤ) : Submodule ℂ (WeightedCoeffPair w p) :=
  Submodule.span ℂ {f | ∃ k : ℤ, k ≠ n ∧ ∃ i : Fin 2, f = sourceSignedFourierMode w k i}

/-- The two resonant coordinates are exactly the amplitudes of the individual signed modes. -/
theorem resonantSynthesis_eq_sourceSignedFourierModes (w : Weight) (k : ℤ) (c : Fin 2 → ℂ) :
    resonantSynthesis w k c = c 0 • sourceSignedFourierMode (p := p) w k 0 + c 1 • sourceSignedFourierMode w k 1 := by
  unfold sourceSignedFourierMode
  rw [← map_smul, ← map_smul, ← map_add]
  congr 1
  funext i
  fin_cases i <;> simp

/-- Every nonresonant pair of amplitudes lies in the algebraic span of the nonresonant modes. -/
theorem resonantSynthesis_mem_sourceNonresonantModeSpan (w : Weight) (n k : ℤ) (hk : k ≠ n) (c : Fin 2 → ℂ) :
    resonantSynthesis w k c ∈ sourceNonresonantModeSpan (p := p) w n := by
  rw [resonantSynthesis_eq_sourceSignedFourierModes]
  exact Submodule.add_mem _
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨k,hk,0,rfl⟩))
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨k,hk,1,rfl⟩))

/-- The full signed Fourier series converges in the original weighted pair norm. -/
theorem sourceSignedFourierModes_hasSum (hp : p ≠ ⊤) (w : Weight) (f : WeightedCoeffPair w p) :
    HasSum (fun k : ℤ => resonantSynthesis w k ![f.fst.val (-k), f.snd.val k]) f := by
  convert weightedSignedPairMode_hasSum hp w f using 1
  funext k
  rfl

/-- A vector is complementary exactly when its two resonant coordinates vanish. -/
theorem complementaryProjection_eq_self_iff_coordinates_zero (w : Weight) (n : ℤ) (f : WeightedCoeffPair w p) :
    complementaryProjection w n f = f ↔ resonantCoordinates w n f = 0 := by
  rw [complementaryProjection_eq_self_iff]
  constructor
  · rintro ⟨hf,hg⟩
    funext i
    fin_cases i <;> simp [hf,hg]
  · intro h
    constructor
    · simpa using congrFun h 0
    · simpa using congrFun h 1

/-- At every finite Banach exponent, the closed nonresonant span is precisely the coordinate kernel. -/
theorem sourceNonresonantModeSpan_closure_eq_ker (hp : p ≠ ⊤) (w : Weight) (n : ℤ) :
    (sourceNonresonantModeSpan (p := p) w n).topologicalClosure =
      (resonantCoordinates (p := p) w n).ker := by
  apply le_antisymm
  · apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro f ⟨k,hk,i,rfl⟩
      change resonantCoordinates w n (sourceSignedFourierMode w k i) = 0
      funext j
      fin_cases j <;> simp [sourceSignedFourierMode, Ne.symm hk]
    · exact (resonantCoordinates w n).isClosed_ker
  · intro f hf
    have hz := (complementaryProjection_eq_self_iff_coordinates_zero w n f).mpr hf
    have hc := (complementaryProjection_eq_self_iff w n f).mp hz
    apply (sourceNonresonantModeSpan (p := p) w n).isClosed_topologicalClosure.mem_of_tendsto
      (sourceSignedFourierModes_hasSum hp w f)
    apply Filter.Eventually.of_forall
    intro S
    apply Submodule.sum_mem
    intro k _
    by_cases hk : k = n
    · subst k
      simpa only [hc.1,hc.2,show (![0,0] : Fin 2 → ℂ) = 0 by ext i; fin_cases i <;> rfl,
        map_zero] using (sourceNonresonantModeSpan (p := p) w n).topologicalClosure.zero_mem
    · exact (sourceNonresonantModeSpan w n).le_topologicalClosure (resonantSynthesis_mem_sourceNonresonantModeSpan w n k hk _)

/-- The finite span of the two individual source modes at index n. -/
def sourceResonantModeSpan (w : Weight) (n : ℤ) : Submodule ℂ (WeightedCoeffPair w p) :=
  Submodule.span ℂ (Set.range (sourceSignedFourierMode w n))

/-- The two-mode span is the actual range of resonant synthesis. -/
theorem sourceResonantModeSpan_eq_range (w : Weight) (n : ℤ) :
    sourceResonantModeSpan (p := p) w n = (resonantSynthesis w n).range := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro f ⟨i,rfl⟩
    exact ⟨Pi.single i 1,rfl⟩
  · rintro f ⟨c,rfl⟩
    change resonantSynthesis w n c ∈ sourceResonantModeSpan w n
    rw [resonantSynthesis_eq_sourceSignedFourierModes]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0,rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1,rfl⟩))

/-- The actual Q projection has the closed nonresonant Fourier span as its range. -/
theorem complementaryProjection_range_eq_sourceClosedSpan (hp : p ≠ ⊤) (w : Weight) (n : ℤ) :
    (complementaryProjection (p := p) w n).range = (sourceNonresonantModeSpan w n).topologicalClosure := by
  rw [sourceNonresonantModeSpan_closure_eq_ker hp]
  ext f
  constructor
  · rintro ⟨g,rfl⟩
    exact resonantCoordinates_complementary w n g
  · intro hf
    exact ⟨f,(complementaryProjection_eq_self_iff_coordinates_zero w n f).mpr hf⟩

/-- The actual P projection has the span of the two source modes as its range. -/
theorem resonantProjection_range_eq_sourceSpan (w : Weight) (n : ℤ) :
    (resonantProjection (p := p) w n).range = sourceResonantModeSpan w n := by
  rw [sourceResonantModeSpan_eq_range]
  ext f
  constructor
  · rintro ⟨g,rfl⟩
    exact ⟨resonantCoordinates w n g,resonantSynthesis_coordinates w n g⟩
  · rintro ⟨c,rfl⟩
    refine ⟨resonantSynthesis w n c,?_⟩
    change resonantProjection w n (resonantSynthesis w n c) = resonantSynthesis w n c
    rw [← resonantSynthesis_coordinates,resonantCoordinates_synthesis]

/-- Equation (1.13) is a topological direct sum with the literal Fourier-mode spans. -/
theorem sourcePQ_isTopCompl (hp : p ≠ ⊤) (w : Weight) (n : ℤ) :
    (sourceResonantModeSpan (p := p) w n).IsTopCompl (sourceNonresonantModeSpan w n).topologicalClosure := by
  rw [sourceResonantModeSpan_eq_range,sourceNonresonantModeSpan_closure_eq_ker hp]
  exact ContinuousLinearMap.isTopCompl_range_ker_of_leftInverse
    (resonantSynthesis w n) (resonantCoordinates w n) (resonantCoordinates_synthesis w n)

/-- The resonant space has complex dimension two, including at the zero index. -/
theorem sourceResonantModeSpan_finrank (w : Weight) (n : ℤ) :
    Module.finrank ℂ (sourceResonantModeSpan (p := p) w n) = 2 := by
  rw [sourceResonantModeSpan_eq_range]
  simpa using LinearMap.finrank_range_of_inj (resonantSynthesis_injective (p := p) w n)

end NLS.ZakharovShabat
