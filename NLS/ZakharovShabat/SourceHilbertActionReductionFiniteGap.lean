import NLS.ZakharovShabat.SourceHilbertAngleHamiltonian
import NLS.ZakharovShabat.SourceFiniteGapNLSHamiltonians
import NLS.ZakharovShabat.SourceFiniteGapActionTrace

/-! # Physical finite-gap Hamiltonians along action reduction

The actual source curve preserves all unselected closed gaps and remains
finite-gap. Its first physical Hamiltonian decreases at unit speed.
-/
noncomputable section
open Set Complex Filter Topology NLS.Poisson
namespace NLS.ZakharovShabat

/-- The first physical Hamiltonian is the original holomorphic Hilbert mass. -/
theorem sourceFiniteGapNLSHamiltonian_one_eq_mass (φ : realTypeSourceSubmodule 2)
    (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) :
    sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) φ hf 1 = sourceHilbertMass φ.val := by
  rw [sourceFiniteGapNLSHamiltonian_one]
  rfl

/-- Any finite set containing the open gaps computes the first physical Hamiltonian. -/
theorem sourceFiniteGapNLSHamiltonian_one_eq_sum (φ : realTypeSourceSubmodule 2)
    (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) (S : Finset ℤ)
    (hS : ∀ k ∉ S, canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential φ.val)
      (periodOnePotential_mem φ.val) k = 0) :
    sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) φ hf 1 =
      ∑ k ∈ S, sourceRealAction (by simp) (by norm_num) φ.val φ.property k := by
  classical
  have hz (k : ℤ) (hk : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential φ.val) (periodOnePotential_mem φ.val) k = 0) :
      sourceRealAction (by simp) (by norm_num) φ.val φ.property k = 0 :=
    (sourceRealAction_nonneg_and_eq_zero_iff_gap_zero (by simp) (by norm_num) φ.val φ.property k).2.2.mpr
      (by simpa only [sourcePeriodicGapDisplacement_apply] using hk)
  rw [sourceFiniteGapNLSHamiltonian_one_eq_mass, ← sourceFiniteGap_sum_actions_eq_mass φ hf]
  calc
    _ = ∑' k : ℤ, sourceRealAction (by simp) (by norm_num) φ.val φ.property k := by
      symm
      apply tsum_eq_sum
      intro k hk
      apply hz k
      by_contra hne
      exact hk ((Set.Finite.mem_toFinset hf).mpr hne)
    _ = _ := tsum_eq_sum (fun k hk => hz k (hS k hk))

namespace SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)} {s : (k : ℤ) → CoeffPair 2 → DeletedCoeff 2 k}

/-- Every unselected closed gap stays closed throughout the source curve. -/
theorem hilbertActionReduction_gap_zero_of_ne
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (n k : ℤ) (hkn : k ≠ n) (t : ℝ)
    (hk : canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential φ.val)
      (periodOnePotential_mem φ.val) k = 0) :
    canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential (D.hilbertActionReduction φ n t).val)
      (periodOnePotential_mem (D.hilbertActionReduction φ n t).val) k = 0 := by
  have hz := sourceRealAction_nonneg_and_eq_zero_iff_gap_zero (by simp) (by norm_num)
    (D.hilbertActionReduction φ n t).val (D.hilbertActionReduction φ n t).property k
  rw [sourcePeriodicGapDisplacement_apply] at hz
  apply hz.2.2.mp
  apply Complex.ext
  · rw [D.hilbertActionReduction_action_ne φ n k hkn t,
      (sourceRealAction_nonneg_and_eq_zero_iff_gap_zero (by simp) (by norm_num) φ.val φ.property k).2.2.mpr
        (by simpa only [sourcePeriodicGapDisplacement_apply] using hk)]
  · exact hz.2.1

/-- Finite-gap is preserved for every time, including the collapse endpoint. -/
theorem hilbertActionReduction_mem_finiteGap
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (n : ℤ) (t : ℝ) :
    D.hilbertActionReduction φ n t ∈ sourceFiniteGapLocus (by simp) (by norm_num) := by
  apply (hf.insert n).subset
  intro k hk
  by_cases hkn : k = n
  · exact Or.inl hkn
  · right
    intro hzero
    exact hk (D.hilbertActionReduction_gap_zero_of_ne φ n k hkn t hzero)

/-- With an open selected gap, no new gap index is introduced. -/
theorem hilbertActionReduction_gap_support
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (n : ℤ) (hn : canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential φ.val)
      (periodOnePotential_mem φ.val) n ≠ 0) (t : ℝ) :
    ∀ k ∉ hf.toFinset, canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (D.hilbertActionReduction φ n t).val)
      (periodOnePotential_mem (D.hilbertActionReduction φ n t).val) k = 0 := by
  intro k hk
  have hkn : k ≠ n := fun he => hk (he ▸ (Set.Finite.mem_toFinset hf).mpr hn)
  apply D.hilbertActionReduction_gap_zero_of_ne φ n k hkn t
  by_contra hne
  exact hk ((Set.Finite.mem_toFinset hf).mpr hne)

/-- The physical mass changes by exactly minus the curve parameter. -/
theorem hilbertActionReduction_physical_mass
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (n : ℤ) (hn : canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential φ.val)
      (periodOnePotential_mem φ.val) n ≠ 0)
    (ha : 0 < (sourceRealAction (by simp) (by norm_num) φ.val φ.property n).re)
    (t : ℝ) (ht : t ≤ (sourceRealAction (by simp) (by norm_num) φ.val φ.property n).re) :
    sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) (D.hilbertActionReduction φ n t)
      (D.hilbertActionReduction_mem_finiteGap φ hf n t) 1 =
        sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) φ hf 1 - (t : ℂ) := by
  classical
  have hsupport : ∀ k ∉ hf.toFinset, canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential φ.val) (periodOnePotential_mem φ.val) k = 0 := by
    intro k hk
    by_contra hne
    exact hk ((Set.Finite.mem_toFinset hf).mpr hne)
  rw [sourceFiniteGapNLSHamiltonian_one_eq_sum _ _ hf.toFinset
    (D.hilbertActionReduction_gap_support φ hf n hn t),
    sourceFiniteGapNLSHamiltonian_one_eq_sum φ hf hf.toFinset hsupport]
  have he (k : ℤ) : sourceRealAction (by simp) (by norm_num)
      (D.hilbertActionReduction φ n t).val (D.hilbertActionReduction φ n t).property k =
      sourceRealAction (by simp) (by norm_num) φ.val φ.property k - if k = n then (t : ℂ) else 0 := by
    have himψ := (sourceRealAction_nonneg_and_eq_zero_iff_gap_zero (by simp) (by norm_num)
      (D.hilbertActionReduction φ n t).val (D.hilbertActionReduction φ n t).property k).2.1
    have himφ := (sourceRealAction_nonneg_and_eq_zero_iff_gap_zero (by simp) (by norm_num)
      φ.val φ.property k).2.1
    by_cases hkn : k = n
    · subst k
      apply Complex.ext
      · simpa using D.hilbertActionReduction_action_same φ n ha t ht
      · simp [himψ, himφ]
    · simp only [if_neg hkn, sub_zero]
      exact Complex.ext (D.hilbertActionReduction_action_ne φ n k hkn t) (himψ.trans himφ.symm)
  simp_rw [he]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq', if_pos ((Set.Finite.mem_toFinset hf).mpr hn)]

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
