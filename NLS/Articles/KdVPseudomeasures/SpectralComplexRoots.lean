import NLS.Articles.KdVPseudomeasures.SpectralComplexPairs
import NLS.SequenceSpaces.OrderedFiniteEnumeration

/-! The actual complex central multiset, sorted in the source lexicographic order. -/
noncomputable section
open Set
open scoped ENNReal Classical
namespace NLS.Articles.KdVPseudomeasures
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue NLS.KdV NLS.ComplexAnalysis

/-- Every actual complex central spectral value has its full physical algebraic repetitions. -/
def sourceComplexCentralRoots (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (N : ℕ) : Multiset ℂ :=
  ∑ z ∈ sourceCentralSpectrum r hr q N,
    Multiset.replicate (sourceHillAlgebraicMultiplicity r hr q z) z

theorem count_sourceComplexCentralRoots (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (N : ℕ) (z : ℂ) :
    (sourceComplexCentralRoots r hr q N).count z =
      if z ∈ sourceCentralSpectrum r hr q N then sourceHillAlgebraicMultiplicity r hr q z else 0 := by
  simp [sourceComplexCentralRoots, Multiset.count_sum', Multiset.count_replicate, eq_comm]

theorem mem_sourceComplexCentralRoots_iff (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (N : ℕ) (z : ℂ) :
    z ∈ sourceComplexCentralRoots r hr q N ↔ z ∈ sourceCentralSpectrum r hr q N := by
  rw [← Multiset.count_pos, count_sourceComplexCentralRoots]
  by_cases hz : z ∈ sourceCentralSpectrum r hr q N
  · simp only [hz, iff_true]
    exact sourceCentral_multiplicity_pos r hr q N z hz
  · simp [hz]

theorem card_sourceComplexCentralRoots (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (N : ℕ) :
    (sourceComplexCentralRoots r hr q N).card = sourceCentralAlgebraicCount r hr q N := by
  simp [sourceComplexCentralRoots, sourceCentralAlgebraicCount]

/-- Sorting the actual central block keeps all algebraic repetitions and the exact source order. -/
theorem exists_ordered_sourceComplexCentralRoots (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (N : ℕ)
    (hc : sourceCentralAlgebraicCount r hr q N = 2*N-1) :
    ∃ ξ : ℕ → ℂ, (∑ j ∈ Finset.range (2*N-1), ({ξ j}:Multiset ℂ)) = sourceComplexCentralRoots r hr q N ∧
      (∀ i < 2*N-1, ∀ j < 2*N-1, i ≤ j → complexLexLE (ξ i) (ξ j)) ∧
      ∀ z : ℂ, (∑ j ∈ Finset.range (2*N-1), if ξ j = z then 1 else 0) =
        if z ∈ sourceCentralSpectrum r hr q N then sourceHillAlgebraicMultiplicity r hr q z else 0 := by
  obtain ⟨ξ, hξ, hord⟩ := NLS.exists_ordered_finset_multiset_enumeration complexLexLE
    (Finset.range (2*N-1)) (sourceComplexCentralRoots r hr q N)
    (by simpa only [Finset.card_range, card_sourceComplexCentralRoots] using hc)
  refine ⟨ξ, hξ, ?_, ?_⟩
  · exact fun i hi j hj hij => hord i (Finset.mem_range.mpr hi) j (Finset.mem_range.mpr hj) hij
  · intro z
    have he := congrArg (fun m : Multiset ℂ => m.count z) hξ
    simpa only [Multiset.count_sum', Multiset.count_singleton, eq_comm, count_sourceComplexCentralRoots] using he

end NLS.Articles.KdVPseudomeasures
