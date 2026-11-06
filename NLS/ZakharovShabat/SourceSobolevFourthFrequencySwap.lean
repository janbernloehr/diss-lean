import NLS.ZakharovShabat.SourceSobolevFourthSwap
import NLS.ZakharovShabat.SourceSobolevFourthFrequency

/-! # Physical frequency reflection, including closed actions

Compare the actual action-reduction and gap-opening Hamiltonians by their
original actions. Physical H₄ parity and full-domain action dependence give
the odd reflected frequency without assuming any angle identity.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The original real action at a native physical H^(3/2) source. -/
def nativeFourthAction (a : NativeFourthSobolevSource) (n : ℤ) : ℝ :=
  (sourceRealAction (by simp) (by norm_num)
    (originalWeightedRealSource fourthSobolevSpectralWeight a).val
    (originalWeightedRealSource fourthSobolevSpectralWeight a).property n).re

theorem nativeFourthAction_componentSwap (a : NativeFourthSobolevSource) (n : ℤ) :
    nativeFourthAction (weightedRealSourceComponentSwap fourthSobolevSpectralWeight a) n =
      nativeFourthAction a (-n) := by
  unfold nativeFourthAction
  simp only [originalWeightedRealSource_componentSwap]
  exact congrArg Complex.re (sourceRealAction_componentSwap (by simp) (by norm_num) _ n)

namespace SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

/-- Reflected original action levels give opposite physical H₄ values on
the whole fractional domain. -/
theorem sourceSobolevFourthHamiltonian_eq_neg_of_reflected_actions
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (a b : NativeFourthSobolevSource)
    (h : ∀ n : ℤ, nativeFourthAction b n = nativeFourthAction a (-n)) :
    sourceSobolevFourthHamiltonian b = -sourceSobolevFourthHamiltonian a := by
  rw [← sourceSobolevFourthHamiltonian_componentSwap]
  apply D.sourceSobolevFourthHamiltonian_eq_of_actions
  intro n
  exact (h n).trans (nativeFourthAction_componentSwap a n).symm

/-- The two actual open-action Hamiltonians have opposite values before
the selected original action collapses. -/
theorem sobolevFourthActionReductionHamiltonian_componentSwap
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (a : NativeFourthSobolevSource) (n : ℤ) (ha : 0 < nativeFourthAction a (-n))
    (t : ℝ) (ht : t ≤ nativeFourthAction a (-n)) :
    D.sobolevFourthActionReductionHamiltonian
      (weightedRealSourceComponentSwap fourthSobolevSpectralWeight a) n t =
      -D.sobolevFourthActionReductionHamiltonian a (-n) t := by
  apply D.sourceSobolevFourthHamiltonian_eq_neg_of_reflected_actions
  intro k
  have hsa : 0 < nativeFourthAction
      (weightedRealSourceComponentSwap fourthSobolevSpectralWeight a) n := by
    rw [nativeFourthAction_componentSwap]
    exact ha
  have hst : t ≤ nativeFourthAction
      (weightedRealSourceComponentSwap fourthSobolevSpectralWeight a) n := by
    rw [nativeFourthAction_componentSwap]
    exact ht
  by_cases hkn : k = n
  · subst k
    exact (D.sobolevActionReduction_action_same (3/2) (by norm_num) _ n hsa t hst).trans
      ((congrArg (fun x : ℝ => x-t) (nativeFourthAction_componentSwap a n)).trans
        (D.sobolevActionReduction_action_same (3/2) (by norm_num) a (-n) ha t ht).symm)
  · have hneg : -k ≠ -n := fun h => hkn (neg_injective h)
    exact (D.sobolevActionReduction_action_ne (3/2) (by norm_num) _ n k hkn t).trans
      ((nativeFourthAction_componentSwap a k).trans
        (D.sobolevActionReduction_action_ne (3/2) (by norm_num) a (-n) (-k) hneg t).symm)

/-- The independent open physical derivative has odd reflected indexing. -/
theorem sobolevFourthOpenFrequency_componentSwap
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (a : NativeFourthSobolevSource) (n : ℤ) (ha : 0 < nativeFourthAction a (-n)) :
    D.sobolevFourthOpenFrequency (weightedRealSourceComponentSwap fourthSobolevSpectralWeight a) n =
      -D.sobolevFourthOpenFrequency a (-n) := by
  have he : D.sobolevFourthActionReductionHamiltonian
      (weightedRealSourceComponentSwap fourthSobolevSpectralWeight a) n =ᶠ[𝓝 0]
      fun t => -D.sobolevFourthActionReductionHamiltonian a (-n) t := by
    filter_upwards [eventually_le_nhds ha] with t ht
    exact D.sobolevFourthActionReductionHamiltonian_componentSwap a n ha t ht
  unfold sobolevFourthOpenFrequency
  rw [he.deriv_eq]
  exact congrArg Neg.neg (deriv.neg (f := D.sobolevFourthActionReductionHamiltonian a (-n)) (x := 0))

/-- At closed actions the actual opening Hamiltonians have opposite values
for every amplitude, with the normalization I=t²/2 retained. -/
theorem sobolevFourthOpeningHamiltonian_componentSwap
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (a : NativeFourthSobolevSource) (n : ℤ)
    (hn : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (originalWeightedRealSource fourthSobolevSpectralWeight a).val)
      (periodOnePotential_mem _) (-n) = 0) :
    D.sobolevFourthOpeningHamiltonian
      (weightedRealSourceComponentSwap fourthSobolevSpectralWeight a) n =
      -D.sobolevFourthOpeningHamiltonian a (-n) := by
  have hsn : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (originalWeightedRealSource fourthSobolevSpectralWeight
        (weightedRealSourceComponentSwap fourthSobolevSpectralWeight a)).val)
      (periodOnePotential_mem _) n = 0 := by
    rw [originalWeightedRealSource_componentSwap]
    exact (sourcePeriodicGap_componentSwap (by simp) (by norm_num) _ n).trans hn
  funext t
  apply D.sourceSobolevFourthHamiltonian_eq_neg_of_reflected_actions
  intro k
  by_cases hkn : k = n
  · subst k
    exact (D.sobolevFourthOpening_action_same_of_closed _ n hsn t).trans
      (D.sobolevFourthOpening_action_same_of_closed a (-n) hn t).symm
  · have hneg : -k ≠ -n := fun h => hkn (neg_injective h)
    have hleft := D.originalWeightedRealSource_sobolevGapOpening_hilbert (3/2) (by norm_num)
      (weightedRealSourceComponentSwap fourthSobolevSpectralWeight a) n t
    have hright := D.originalWeightedRealSource_sobolevGapOpening_hilbert (3/2) (by norm_num) a (-n) t
    let I : realTypeSourceSubmodule 2 → ℤ → ℝ := fun φ j =>
      (sourceRealAction (by simp) (by norm_num) φ.val φ.property j).re
    have hl : nativeFourthAction (D.sobolevGapOpening (by rfl) (3/2) (by norm_num)
        (weightedRealSourceComponentSwap fourthSobolevSpectralWeight a) n t) k =
        nativeFourthAction (weightedRealSourceComponentSwap fourthSobolevSpectralWeight a) k :=
      (congrArg (fun φ => I φ k) hleft).trans (D.hilbertGapOpening_action_ne _ n k hkn t)
    have hr : nativeFourthAction (D.sobolevGapOpening (by rfl) (3/2) (by norm_num) a (-n) t) (-k) =
        nativeFourthAction a (-k) :=
      (congrArg (fun φ => I φ (-k)) hright).trans (D.hilbertGapOpening_action_ne _ (-n) (-k) hneg t)
    exact hl.trans ((nativeFourthAction_componentSwap a k).trans hr.symm)

/-- The independent second physical amplitude derivative has the same
odd reflection at every closed action. -/
theorem sobolevFourthClosedFrequency_componentSwap
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (a : NativeFourthSobolevSource) (n : ℤ)
    (hn : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (originalWeightedRealSource fourthSobolevSpectralWeight a).val)
      (periodOnePotential_mem _) (-n) = 0) :
    D.sobolevFourthClosedFrequency (weightedRealSourceComponentSwap fourthSobolevSpectralWeight a) n =
      -D.sobolevFourthClosedFrequency a (-n) := by
  unfold sobolevFourthClosedFrequency
  rw [D.sobolevFourthOpeningHamiltonian_componentSwap a n hn,deriv.neg']
  exact deriv.neg (f := deriv (D.sobolevFourthOpeningHamiltonian a (-n))) (x := 0)

/-- Full-domain reflection of the independently defined physical H₄
frequencies, including all collapsed gaps. -/
theorem sobolevFourthFrequency_componentSwap
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (a : NativeFourthSobolevSource) (n : ℤ) :
    D.sobolevFourthFrequency (weightedRealSourceComponentSwap fourthSobolevSpectralWeight a) n =
      -D.sobolevFourthFrequency a (-n) := by
  have hgap : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (originalWeightedRealSource fourthSobolevSpectralWeight
        (weightedRealSourceComponentSwap fourthSobolevSpectralWeight a)).val)
      (periodOnePotential_mem _) n =
      canonicalPeriodicGap (by simp) (by norm_num)
        (periodOnePotential (originalWeightedRealSource fourthSobolevSpectralWeight a).val)
        (periodOnePotential_mem _) (-n) := by
    rw [originalWeightedRealSource_componentSwap]
    exact sourcePeriodicGap_componentSwap (by simp) (by norm_num) _ n
  unfold sobolevFourthFrequency
  rw [hgap]
  split_ifs with hn
  · exact D.sobolevFourthClosedFrequency_componentSwap a n hn
  · apply D.sobolevFourthOpenFrequency_componentSwap
    have hpos := sourceRealAction_nonneg_and_eq_zero_iff_gap_zero (by simp) (by norm_num)
      (originalWeightedRealSource fourthSobolevSpectralWeight a).val
      (originalWeightedRealSource fourthSobolevSpectralWeight a).property (-n)
    rw [sourcePeriodicGapDisplacement_apply] at hpos
    apply lt_of_le_of_ne hpos.1
    intro hz
    apply hn
    apply hpos.2.2.mp
    apply Complex.ext
    · exact hz.symm
    · exact hpos.2.1

/-- On the actual equal-field mKdV diagonal the physical H₄ frequency is
odd in its signed index, on the entire fractional domain. -/
theorem sobolevFourthFrequency_odd_of_diagonal
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (a : NativeFourthSobolevSource) (ha : a.val.fst = a.val.snd) (n : ℤ) :
    D.sobolevFourthFrequency a (-n) = -D.sobolevFourthFrequency a n := by
  have he := D.sobolevFourthFrequency_componentSwap a (-n)
  rw [(weightedRealSourceComponentSwap_eq_self_iff fourthSobolevSpectralWeight a).mpr ha,
    neg_neg] at he
  exact he

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
