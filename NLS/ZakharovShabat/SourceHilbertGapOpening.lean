import NLS.SequenceSpaces.RealActionOpening
import NLS.ZakharovShabat.SourceHilbertActionReductionFiniteGap

/-! # An actual one-gap opening curve

Pull back a single real Birkhoff coordinate line by the global analytic
inverse. At a collapsed selected gap every nonzero amplitude opens that
gap, all other actions are fixed, and finite gap support is preserved.
-/
noncomputable section
open Set Metric Filter Topology Complex
namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)} {s : (k : ℤ) → CoeffPair 2 → DeletedCoeff 2 k}

def hilbertGapOpening
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (n : ℤ) (t : ℝ) : realTypeSourceSubmodule 2 :=
  D.hilbertRealHomeomorph.symm (RealCoeff.actionOpening (D.hilbertRealHomeomorph φ) n t)

@[simp] theorem hilbertRealHomeomorph_gapOpening
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (n : ℤ) (t : ℝ) :
    D.hilbertRealHomeomorph (D.hilbertGapOpening φ n t) =
      RealCoeff.actionOpening (D.hilbertRealHomeomorph φ) n t :=
  D.hilbertRealHomeomorph.apply_symm_apply _

@[simp] theorem hilbertGapOpening_zero
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (n : ℤ) : D.hilbertGapOpening φ n 0 = φ := by
  simp only [hilbertGapOpening,RealCoeff.actionOpening_zero]
  exact D.hilbertRealHomeomorph.symm_apply_apply φ

theorem analyticOnNhd_hilbertGapOpening
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (n : ℤ) :
    AnalyticOnNhd ℝ (D.hilbertGapOpening φ n) univ := by
  intro t _
  exact (D.hilbertRealHomeomorph_symm_analytic _ (mem_univ _)).comp
    (RealCoeff.analyticOnNhd_actionOpening _ n t (mem_univ _))

theorem continuous_hilbertGapOpening
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (n : ℤ) : Continuous (D.hilbertGapOpening φ n) :=
  continuous_iff_continuousAt.mpr fun t => (D.analyticOnNhd_hilbertGapOpening φ n t (mem_univ _)).continuousAt

/-- No unselected coordinate pair, and hence no unselected action, changes. -/
theorem hilbertGapOpening_action_ne
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (n k : ℤ) (hkn : k ≠ n) (t : ℝ) :
    (sourceRealAction (by simp) (by norm_num) (D.hilbertGapOpening φ n t).val
      (D.hilbertGapOpening φ n t).property k).re =
      (sourceRealAction (by simp) (by norm_num) φ.val φ.property k).re := by
  rw [← D.hilbert_pairAction_eq,hilbertRealHomeomorph_gapOpening,
    RealCoeff.pairAction_actionOpening_ne _ n k hkn t,D.hilbert_pairAction_eq]

theorem hilbertGapOpening_gap_zero_iff_of_ne
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (n k : ℤ) (hkn : k ≠ n) (t : ℝ) :
    canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential (D.hilbertGapOpening φ n t).val)
      (periodOnePotential_mem (D.hilbertGapOpening φ n t).val) k = 0 ↔
    canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential φ.val) (periodOnePotential_mem φ.val) k = 0 := by
  have hψ := D.real_coordinates_zero_iff_gap_zero (D.hilbertGapOpening φ n t) k
  have hφ := D.real_coordinates_zero_iff_gap_zero φ k
  rw [sourcePeriodicGapDisplacement_apply] at hψ hφ
  change (((D.hilbertRealHomeomorph (D.hilbertGapOpening φ n t)).1 k = 0) ∧
    ((D.hilbertRealHomeomorph (D.hilbertGapOpening φ n t)).2 k = 0)) ↔ _ at hψ
  rw [hilbertRealHomeomorph_gapOpening,(RealCoeff.actionOpening_apply_ne _ n k hkn t).1,
    (RealCoeff.actionOpening_apply_ne _ n k hkn t).2] at hψ
  exact hψ.symm.trans hφ

theorem hilbertGapOpening_action_same_of_closed
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (n : ℤ)
    (hn : canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential φ.val)
      (periodOnePotential_mem φ.val) n = 0) (t : ℝ) :
    (sourceRealAction (by simp) (by norm_num) (D.hilbertGapOpening φ n t).val
      (D.hilbertGapOpening φ n t).property n).re = t^2/2 := by
  rw [← D.hilbert_pairAction_eq,hilbertRealHomeomorph_gapOpening]
  apply RealCoeff.pairAction_actionOpening_same
  exact (D.real_coordinates_zero_iff_gap_zero φ n).mpr
    (by simpa only [sourcePeriodicGapDisplacement_apply] using hn)

/-- Every nonzero amplitude opens the selected collapsed gap. -/
theorem hilbertGapOpening_gap_ne_zero
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (n : ℤ)
    (hn : canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential φ.val)
      (periodOnePotential_mem φ.val) n = 0) (t : ℝ) (ht : t ≠ 0) :
    canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential (D.hilbertGapOpening φ n t).val)
      (periodOnePotential_mem (D.hilbertGapOpening φ n t).val) n ≠ 0 := by
  intro hz
  have hzero := (sourceRealAction_nonneg_and_eq_zero_iff_gap_zero (by simp) (by norm_num)
    (D.hilbertGapOpening φ n t).val (D.hilbertGapOpening φ n t).property n).2.2.mpr
      (by simpa only [sourcePeriodicGapDisplacement_apply] using hz)
  have he := D.hilbertGapOpening_action_same_of_closed φ n hn t
  rw [hzero,Complex.zero_re] at he
  have := sq_pos_of_ne_zero ht
  linarith

/-- Only the original open-gap indices and the selected index can be open. -/
theorem hilbertGapOpening_gap_support
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (n : ℤ) (t : ℝ) :
    ∀ k ∉ insert n hf.toFinset, canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (D.hilbertGapOpening φ n t).val)
      (periodOnePotential_mem (D.hilbertGapOpening φ n t).val) k = 0 := by
  classical
  intro k hk
  have hkn : k ≠ n := fun he => hk (Finset.mem_insert.mpr (Or.inl he))
  apply (D.hilbertGapOpening_gap_zero_iff_of_ne φ n k hkn t).mpr
  by_contra hne
  exact hk (Finset.mem_insert.mpr (Or.inr ((Set.Finite.mem_toFinset hf).mpr hne)))

theorem hilbertGapOpening_mem_finiteGap
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (n : ℤ) (t : ℝ) : D.hilbertGapOpening φ n t ∈ sourceFiniteGapLocus (by simp) (by norm_num) := by
  classical
  apply (insert n hf.toFinset).finite_toSet.subset
  intro k hk
  by_contra hnot
  exact hk (D.hilbertGapOpening_gap_support φ hf n t k hnot)

/-- The action-reduction curve through an opened source stays on the same
amplitude line, with the exact square-root change of parameter. -/
theorem hilbertActionReduction_gapOpening
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (n : ℤ)
    (hn : canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential φ.val)
      (periodOnePotential_mem φ.val) n = 0) (t u : ℝ) :
    D.hilbertActionReduction (D.hilbertGapOpening φ n t) n u =
      D.hilbertGapOpening φ n (t*RealCoeff.actionReductionScale (t^2/2) u) := by
  apply D.hilbertRealHomeomorph.injective
  rw [D.hilbertRealHomeomorph_actionReduction,hilbertRealHomeomorph_gapOpening,
    RealCoeff.actionReduction_actionOpening,hilbertRealHomeomorph_gapOpening]
  exact (D.real_coordinates_zero_iff_gap_zero φ n).mpr
    (by simpa only [sourcePeriodicGapDisplacement_apply] using hn)

end NLS.ZakharovShabat.SourceBirkhoffMapComplexData
