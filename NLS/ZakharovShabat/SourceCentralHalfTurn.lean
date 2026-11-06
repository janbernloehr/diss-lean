import NLS.ZakharovShabat.SourceActionFlowComponentSwap
import NLS.SequenceSpaces.RealActionHalfTurn

/-! # The complete central half turn preserves the physical diagonal -/
noncomputable section
open Set Complex NLS.Poisson
namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)} {s : (k : ℤ) → CoeffPair 2 → DeletedCoeff 2 k}

theorem continuous_hilbertActionRotation_initial
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s) (k : ℤ) (t : ℝ) :
    Continuous (fun φ => D.hilbertActionRotation φ k t) :=
  D.hilbertRealHomeomorph.symm.continuous.comp
    ((RealCoeff.continuous_actionRotation k).comp (continuous_const.prodMk D.hilbertRealHomeomorph.continuous))

theorem hilbertActionRotation_pi_eq_neg_pi
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (k : ℤ) :
    D.hilbertActionRotation φ k Real.pi = D.hilbertActionRotation φ k (-Real.pi) := by
  apply D.hilbertRealHomeomorph.injective
  rw [D.hilbertRealHomeomorph_actionRotation,D.hilbertRealHomeomorph_actionRotation]
  exact RealCoeff.actionRotation_pi_eq_neg_pi _ k

/-- Component exchange and time reversal agree at a half turn, so the
central half turn preserves every original equal-component real source. -/
theorem hilbertCentralHalfTurn_diagonal
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (hφ : φ.val.fst = φ.val.snd) :
    (D.hilbertActionRotation φ 0 Real.pi).val.fst = (D.hilbertActionRotation φ 0 Real.pi).val.snd := by
  have hP : realSourceComponentSwap φ = φ := Subtype.ext ((sourceComponentSwap_eq_self_iff _).mpr hφ)
  have h := D.hilbertActionRotation_componentSwap φ 0 Real.pi
  rw [hP,neg_zero,← D.hilbertActionRotation_pi_eq_neg_pi] at h
  exact (sourceComponentSwap_eq_self_iff _).mp (congrArg Subtype.val h)

/-- Every original signed action is fixed along a complete single action
rotation, in the full summable sequence norm. -/
theorem hilbert_actionSequence_actionRotation
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (k : ℤ) (t : ℝ) :
    sourceHilbertActionSequence s (D.hilbertActionRotation φ k t).val = sourceHilbertActionSequence s φ.val := by
  ext n
  rw [D.hilbert_actionSequence_apply _ (D.real_subset (D.hilbertActionRotation φ k t).property),
    D.hilbert_actionSequence_apply _ (D.real_subset φ.property),
    sourceComplexAction_eq_sourceRealAction (by simp) (by norm_num) n _ (D.hilbertActionRotation φ k t).property,
    sourceComplexAction_eq_sourceRealAction (by simp) (by norm_num) n _ φ.property]
  exact sourceRealAction_eq_of_isospectral (by simp) (by norm_num) _ _
    (D.hilbertActionRotation_mem_isospectralSet φ k t) n

theorem hilbertActionRotation_pi_eq_self_iff_action_zero
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (k : ℤ) :
    D.hilbertActionRotation φ k Real.pi = φ ↔ sourceComplexAction (by simp) (by norm_num) k φ.val = 0 := by
  have hcoord : D.hilbertActionRotation φ k Real.pi = φ ↔
      RealCoeff.pairAction (D.hilbertRealHomeomorph φ) k = 0 := by
    constructor
    · intro h
      apply (RealCoeff.actionRotation_pi_eq_self_iff _ k).mp
      simpa only [D.hilbertRealHomeomorph_actionRotation] using congrArg D.hilbertRealHomeomorph h
    · intro h
      apply D.hilbertRealHomeomorph.injective
      rw [D.hilbertRealHomeomorph_actionRotation]
      exact (RealCoeff.actionRotation_pi_eq_self_iff _ k).mpr h
  change _ ↔ sourceComplexAction (by simp) (by norm_num) k φ.val = 0
  rw [hcoord]
  change RealCoeff.pairAction (sourceRealBirkhoffMap (by simp) (by norm_num) s φ) k = 0 ↔ _
  rw [D.real_pairAction_eq,sourceComplexAction_eq_sourceRealAction (by simp) (by norm_num) k φ.val φ.property]
  have hi := (sourceRealAction_nonneg_and_eq_zero_iff_gap_zero (by simp) (by norm_num) φ.val φ.property k).2.1
  constructor
  · intro h; exact Complex.ext h hi
  · intro h; simp only [h,Complex.zero_re]

end NLS.ZakharovShabat.SourceBirkhoffMapComplexData
