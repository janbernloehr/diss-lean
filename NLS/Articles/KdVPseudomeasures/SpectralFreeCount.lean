import NLS.Articles.KdVPseudomeasures.SpectralCentralWindow
import NLS.KdV.SingularHillFreeSpectrum

/-!
# The actual free central algebraic count

The count uses the original H1/H-minus-one singular operator and its actual
full root spaces. There is one constant mode and two modes for each positive
free value. No invariance under a change of potential is assumed.
-/
noncomputable section
open Set
open scoped ENNReal Classical
namespace NLS.Articles.KdVPseudomeasures
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue NLS.KdV

@[simp] theorem sourceComplexHminusOne_zero (r : ℝ) (hr : AdmissiblePredualOrder r) :
    sourceComplexHminusOne r hr 0 = 0 :=
  (sourceHminusOneInclusion r hr).map_zero

/-- The full physical zero-potential spectrum consists exactly of the free Fourier values. -/
theorem sourceHillSpectrum_zero_mem_iff (r : ℝ) (hr : AdmissiblePredualOrder r) (z : ℂ) :
    z ∈ sourceHillSpectrum r hr 0 ↔ ∃ n : ℕ, z = (freeHillValue n:ℂ) := by
  rw [sourceHillSpectrum_mem_iff,sourceComplexHminusOne_zero,singularHill_zero_eigenvalue_iff]

/-- The constant mode has actual full physical algebraic multiplicity one. -/
theorem sourceHillAlgebraicMultiplicity_zero_zero (r : ℝ) (hr : AdmissiblePredualOrder r) :
    sourceHillAlgebraicMultiplicity r hr 0 0 = 1 := by
  rw [sourceHillAlgebraicMultiplicity_eq_geometric r hr 0 (by
    ext f
    change (0:ℂ) = star (0:ℂ)
    simp),sourceComplexHminusOne_zero,finrank_singularHillEigenspace_zero]

/-- Each positive free value has actual full physical algebraic multiplicity two. -/
theorem sourceHillAlgebraicMultiplicity_zero_free (r : ℝ) (hr : AdmissiblePredualOrder r)
    (n : ℕ) (hn : 1 ≤ n) :
    sourceHillAlgebraicMultiplicity r hr 0 (freeHillValue n:ℂ) = 2 := by
  rw [sourceHillAlgebraicMultiplicity_eq_geometric r hr 0 (by
    ext f
    change (0:ℂ) = star (0:ℂ)
    simp),sourceComplexHminusOne_zero,finrank_singularHillEigenspace_free n hn]

/-- The complete free multiplicity sequence includes the exceptional constant mode. -/
theorem sourceHillAlgebraicMultiplicity_zero_formula (r : ℝ) (hr : AdmissiblePredualOrder r)
    (n : ℕ) : sourceHillAlgebraicMultiplicity r hr 0 (freeHillValue n:ℂ) =
      if n = 0 then 1 else 2 := by
  by_cases hn : n = 0
  · subst n
    simpa [freeHillValue] using sourceHillAlgebraicMultiplicity_zero_zero r hr
  · simpa only [if_neg hn] using sourceHillAlgebraicMultiplicity_zero_free r hr n (by omega)

/-- The actual central boundary cuts the free spectrum at precisely the unsigned mode N. -/
theorem sourceFreeValue_lt_centralEdge_iff (N : ℕ) (hN : 2 ≤ N) (n : ℕ) :
    freeHillValue n < freeHillValue N-12*(N:ℝ) ↔ n < N := by
  have he := freeHillCentralEdge_between N hN
  constructor
  · intro h
    by_contra hn
    have hle := strictMono_freeHillValues.monotone (show N ≤ n by omega)
    linarith
  · intro hn
    exact (strictMono_freeHillValues.monotone (show n ≤ N-1 by omega)).trans_lt he.1

/-- Membership in the free central spectrum is exactly one of the first N free values. -/
theorem mem_sourceCentralSpectrum_zero_iff (r : ℝ) (hr : AdmissiblePredualOrder r)
    (N : ℕ) (hN : 2 ≤ N) (z : ℂ) :
    z ∈ sourceCentralSpectrum r hr 0 N ↔ ∃ n < N, z = (freeHillValue n:ℂ) := by
  rw [mem_sourceCentralSpectrum,sourceHillSpectrum_zero_mem_iff]
  constructor
  · rintro ⟨⟨n,rfl⟩,hn⟩
    exact ⟨n,(sourceFreeValue_lt_centralEdge_iff N hN n).mp hn,rfl⟩
  · rintro ⟨n,hn,rfl⟩
    exact ⟨⟨n,rfl⟩,(sourceFreeValue_lt_centralEdge_iff N hN n).mpr hn⟩

/-- An exact finite-set enumeration of the actual free central spectrum. -/
theorem sourceCentralSpectrum_zero_eq (r : ℝ) (hr : AdmissiblePredualOrder r)
    (N : ℕ) (hN : 2 ≤ N) : sourceCentralSpectrum r hr 0 N =
      (Finset.range N).image (fun n : ℕ => (freeHillValue n:ℂ)) := by
  ext z
  simp only [mem_sourceCentralSpectrum_zero_iff r hr N hN,Finset.mem_image,Finset.mem_range]
  exact exists_congr fun n => and_congr_right fun _ => eq_comm

/-- The free original singular operator has exactly 2N-1 central eigenvalues
counted with its ACTUAL physical algebraic multiplicities. -/
theorem sourceCentralAlgebraicCount_zero (r : ℝ) (hr : AdmissiblePredualOrder r)
    (N : ℕ) (hN : 2 ≤ N) : sourceCentralAlgebraicCount r hr 0 N = 2*N-1 := by
  unfold sourceCentralAlgebraicCount
  rw [sourceCentralSpectrum_zero_eq r hr N hN,Finset.sum_image]
  · simp_rw [sourceHillAlgebraicMultiplicity_zero_formula]
    obtain ⟨M,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show N ≠ 0 by omega)
    rw [Finset.sum_range_succ']
    simp
    omega
  · intro m _ n _ he
    exact strictMono_freeHillValues.injective (Complex.ofReal_injective he)

end NLS.Articles.KdVPseudomeasures
