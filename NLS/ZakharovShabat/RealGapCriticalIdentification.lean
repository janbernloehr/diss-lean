import NLS.ZakharovShabat.RealGapCriticalPoints
import NLS.SequenceSpaces.FiniteMultisetSaturation

/-!
# Identifying every gap witness with its canonical critical index

One distinct critical witness per central gap already gives the full
central critical count. The resulting multiset is therefore exhaustive.
Uniqueness of ordered finite enumerations identifies each witness with
the canonical critical coordinate at the same signed index.
-/

noncomputable section
open Set Complex
open NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- At a common cutoff the distinct gap witnesses exhaust the full central critical multiset. -/
theorem realGapCriticalPoint_centralRoots_eq (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (heven : φ ∈ pairParitySubspace 0) (hreal : IsRealType φ) (K : ℕ)
    (hKP : canonicalPeriodicCutoff hp hp1 φ heven ≤ K)
    (hKC : canonicalCriticalCutoff hp hp1 φ heven ≤ K) :
    (∑ n ∈ Finset.Icc (-(K : ℤ)) K, ({(realGapCriticalPoint hp hp1 φ heven hreal n : ℂ)} : Multiset ℂ)) =
      centralCriticalRoots hp hp1 φ heven K := by
  apply NLS.sum_singleton_eq_of_injective_mem_card
    (Finset.Icc (-(K : ℤ)) K) (fun n => (realGapCriticalPoint hp hp1 φ heven hreal n : ℂ))
    (centralCriticalRoots hp hp1 φ heven K) (realGapCriticalPoint_complex_injective hp hp1 φ heven hreal)
  · intro n hn
    exact realGapCriticalPoint_mem_centralRoots hp hp1 φ heven hreal K hKP n
      (by simp only [Finset.mem_Icc] at hn; omega)
  · rw [← (canonicalCriticalPoints_spec hp hp1 φ heven).1.central_at_larger_cutoff K hKC]
    simp

/-- Each gap witness is the canonical critical coordinate with the same signed index. -/
theorem canonicalCriticalPoints_eq_realGapCriticalPoint (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (heven : φ ∈ pairParitySubspace 0) (hreal : IsRealType φ) (n : ℤ) :
    canonicalCriticalPoints hp hp1 φ heven n = (realGapCriticalPoint hp hp1 φ heven hreal n : ℂ) := by
  let K := max (max (canonicalPeriodicCutoff hp hp1 φ heven)
    (canonicalCriticalCutoff hp hp1 φ heven)) n.natAbs
  have hKP : canonicalPeriodicCutoff hp hp1 φ heven ≤ K := (le_max_left _ _).trans (le_max_left _ _)
  have hKC : canonicalCriticalCutoff hp hp1 φ heven ≤ K := (le_max_right _ _).trans (le_max_left _ _)
  have he := (realGapCriticalPoint_centralRoots_eq hp hp1 φ heven hreal K hKP hKC).trans
    ((canonicalCriticalPoints_spec hp hp1 φ heven).1.central_at_larger_cutoff K hKC).symm
  have hu := NLS.ordered_finset_multiset_enumeration_unique complexLexLE (Finset.Icc (-(K : ℤ)) K)
    (fun i => (realGapCriticalPoint hp hp1 φ heven hreal i : ℂ)) (canonicalCriticalPoints hp hp1 φ heven) he
    (fun i _ j _ hij => (complexLexLE_ofReal_iff _ _).mpr
      ((strictMono_realGapCriticalPoint hp hp1 φ heven hreal).monotone hij))
    (fun _ _ _ _ hij => monotone_canonicalCriticalPoints hp hp1 φ heven hij)
  exact (hu n (by simp only [Finset.mem_Icc]; have hn : n.natAbs ≤ K := le_max_right _ _; omega)).symm

/-- Every canonical critical coordinate lies in its own canonical periodic gap, including central indices. -/
theorem canonicalCriticalPoints_mem_canonicalPeriodicGap (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (heven : φ ∈ pairParitySubspace 0) (hreal : IsRealType φ) (n : ℤ) :
    (canonicalCriticalPoints hp hp1 φ heven n).re ∈
      Icc (canonicalPeriodicLeft hp hp1 φ heven n).re (canonicalPeriodicRight hp hp1 φ heven n).re := by
  rw [canonicalCriticalPoints_eq_realGapCriticalPoint hp hp1 φ heven hreal n,Complex.ofReal_re]
  exact (realGapCriticalPoint_spec hp hp1 φ heven hreal n).1

/-- The real canonical critical sequence is strictly increasing at real-type potentials. -/
theorem strictMono_canonicalCriticalPoints_re_of_realType (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (heven : φ ∈ pairParitySubspace 0) (hreal : IsRealType φ) :
    StrictMono (fun n => (canonicalCriticalPoints hp hp1 φ heven n).re) := by
  intro i j hij
  change (canonicalCriticalPoints hp hp1 φ heven i).re < (canonicalCriticalPoints hp hp1 φ heven j).re
  rw [canonicalCriticalPoints_eq_realGapCriticalPoint hp hp1 φ heven hreal i,
    canonicalCriticalPoints_eq_realGapCriticalPoint hp hp1 φ heven hreal j]
  exact strictMono_realGapCriticalPoint hp hp1 φ heven hreal hij

/-- Canonical critical points have no repeated values at real-type potentials. -/
theorem canonicalCriticalPoints_injective_of_realType (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (heven : φ ∈ pairParitySubspace 0) (hreal : IsRealType φ) :
    Function.Injective (canonicalCriticalPoints hp hp1 φ heven) := by
  intro i j he
  exact (strictMono_canonicalCriticalPoints_re_of_realType hp hp1 φ heven hreal).injective (congrArg re he)

end NLS.ZakharovShabat
