import NLS.Articles.KdVPseudomeasures.SpectralCentralCounting
import NLS.SequenceSpaces.OrderedFiniteEnumeration

/-! The actual finite central spectrum as a multiset with physical algebraic repetitions. -/
noncomputable section
open Set
open scoped ENNReal Classical
namespace NLS.Articles.KdVPseudomeasures
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue NLS.KdV

/-- Every central spectral value is repeated according to its actual full physical root-space dimension. -/
def sourceCentralRoots (r : ℝ) (hr : AdmissiblePredualOrder r) (q : Potential r) (N : ℕ) : Multiset ℂ :=
  ∑ z ∈ sourceCentralSpectrum r hr q.val N,
    Multiset.replicate (sourceHillAlgebraicMultiplicity r hr q.val z) z

/-- The exact physical multiplicity of every central value, and zero elsewhere. -/
theorem count_sourceCentralRoots (r : ℝ) (hr : AdmissiblePredualOrder r) (q : Potential r)
    (N : ℕ) (z : ℂ) : (sourceCentralRoots r hr q N).count z =
      if z ∈ sourceCentralSpectrum r hr q.val N then sourceHillAlgebraicMultiplicity r hr q.val z else 0 := by
  simp [sourceCentralRoots,Multiset.count_sum',Multiset.count_replicate,eq_comm]

/-- Multiset membership is actual membership in the full original central spectrum. -/
theorem mem_sourceCentralRoots_iff (r : ℝ) (hr : AdmissiblePredualOrder r) (q : Potential r)
    (N : ℕ) (z : ℂ) : z ∈ sourceCentralRoots r hr q N ↔ z ∈ sourceCentralSpectrum r hr q.val N := by
  rw [← Multiset.count_pos,count_sourceCentralRoots]
  by_cases hz : z ∈ sourceCentralSpectrum r hr q.val N
  · simp only [hz,iff_true]
    exact sourceCentral_multiplicity_pos r hr q.val N z hz
  · simp [hz]

/-- The multiset cardinality is the existing actual physical algebraic count. -/
theorem card_sourceCentralRoots (r : ℝ) (hr : AdmissiblePredualOrder r) (q : Potential r) (N : ℕ) :
    (sourceCentralRoots r hr q N).card = sourceCentralAlgebraicCount r hr q.val N := by
  simp [sourceCentralRoots,sourceCentralAlgebraicCount]

/-- The same actual central values, in their native real order. -/
def sourceRealCentralRoots (r : ℝ) (hr : AdmissiblePredualOrder r) (q : Potential r) (N : ℕ) : Multiset ℝ :=
  (sourceCentralRoots r hr q N).map Complex.re

/-- Native reality makes real-part transport lossless, including actual algebraic multiplicities. -/
theorem map_ofReal_sourceRealCentralRoots (r : ℝ) (hr : AdmissiblePredualOrder r) (q : Potential r) (N : ℕ) :
    (sourceRealCentralRoots r hr q N).map Complex.ofReal = sourceCentralRoots r hr q N := by
  rw [sourceRealCentralRoots,Multiset.map_map]
  calc
    _ = (sourceCentralRoots r hr q N).map id := by
      apply Multiset.map_congr rfl
      intro z hz
      have hspec := ((mem_sourceCentralSpectrum r hr q.val N z).mp
        ((mem_sourceCentralRoots_iff r hr q N z).mp hz)).1
      have him := sourceHillSpectrum_ofPotential_real r hr q z hspec
      apply Complex.ext <;> simp [him]
    _ = _ := Multiset.map_id _

theorem count_sourceRealCentralRoots (r : ℝ) (hr : AdmissiblePredualOrder r) (q : Potential r)
    (N : ℕ) (x : ℝ) : (sourceRealCentralRoots r hr q N).count x =
      if (x:ℂ) ∈ sourceCentralSpectrum r hr q.val N then sourceHillAlgebraicMultiplicity r hr q.val x else 0 := by
  rw [← count_sourceCentralRoots r hr q N x,← map_ofReal_sourceRealCentralRoots r hr q N]
  exact (Multiset.count_map_eq_count' Complex.ofReal _ Complex.ofReal_injective x).symm

theorem mem_sourceRealCentralRoots_iff (r : ℝ) (hr : AdmissiblePredualOrder r) (q : Potential r)
    (N : ℕ) (x : ℝ) : x ∈ sourceRealCentralRoots r hr q N ↔ (x:ℂ) ∈ sourceCentralSpectrum r hr q.val N := by
  rw [← mem_sourceCentralRoots_iff r hr q N x,← map_ofReal_sourceRealCentralRoots r hr q N]
  exact (Multiset.mem_map_of_injective Complex.ofReal_injective).symm

/-- The real central list has exactly 2N-1 entries with their actual repetitions. -/
theorem card_sourceRealCentralRoots (r : ℝ) (hr : AdmissiblePredualOrder r) (q : Potential r)
    (N : ℕ) (hN : 2 ≤ N)
    (hs : 13*endpointHillConstant r*(N:ℝ)^(r-1/2)*‖q.val‖ ≤ 1/2) :
    (sourceRealCentralRoots r hr q N).card = 2*N-1 := by
  rw [sourceRealCentralRoots,Multiset.card_map,card_sourceCentralRoots]
  exact sourceCentralAlgebraicCount_eq r hr ‖q.val‖ N hN hs q.val le_rfl q.property.1

/-- Sorting the actual central multiset retains every original physical repetition. -/
theorem exists_ordered_sourceCentralRoots (r : ℝ) (hr : AdmissiblePredualOrder r) (q : Potential r)
    (N : ℕ) (hN : 2 ≤ N)
    (hs : 13*endpointHillConstant r*(N:ℝ)^(r-1/2)*‖q.val‖ ≤ 1/2) :
    ∃ ξ : ℕ → ℝ, (∑ j ∈ Finset.range (2*N-1), ({ξ j}:Multiset ℝ)) = sourceRealCentralRoots r hr q N ∧
      (∀ i < 2*N-1, ∀ j < 2*N-1, i ≤ j → ξ i ≤ ξ j) ∧
      ∀ x : ℝ, (∑ j ∈ Finset.range (2*N-1), if ξ j = x then 1 else 0) =
        if (x:ℂ) ∈ sourceCentralSpectrum r hr q.val N then sourceHillAlgebraicMultiplicity r hr q.val x else 0 := by
  obtain ⟨ξ,hξ,hord⟩ := NLS.exists_ordered_finset_multiset_enumeration (· ≤ ·)
    (Finset.range (2*N-1)) (sourceRealCentralRoots r hr q N)
    (by simpa only [Finset.card_range] using card_sourceRealCentralRoots r hr q N hN hs)
  refine ⟨ξ,hξ,?_,?_⟩
  · exact fun i hi j hj hij => hord i (Finset.mem_range.mpr hi) j (Finset.mem_range.mpr hj) hij
  · intro x
    have he := congrArg (fun m : Multiset ℝ => m.count x) hξ
    simpa only [Multiset.count_sum',Multiset.count_singleton,eq_comm,count_sourceRealCentralRoots] using he

end NLS.Articles.KdVPseudomeasures
