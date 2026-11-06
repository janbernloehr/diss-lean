import NLS.ZakharovShabat.SourceActionFlowComponentSwap
import NLS.SequenceSpaces.ReflectionFixedCentralAmbiguity
import NLS.ZakharovShabat.SourceActionTorus

/-! # Positive coordinates of diagonal sources on an original NLS action fiber

Equal positive coordinate pairs leave at most the central half turn.
If the central action is closed, the original source is unique.
-/
noncomputable section
open Set Complex
namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)} {s : (k : ℤ) → CoeffPair 2 → DeletedCoeff 2 k}

theorem diagonal_eq_or_central_halfTurn
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ ψ : realTypeSourceSubmodule 2) (hφ : φ.val.fst = φ.val.snd) (hψ : ψ.val.fst = ψ.val.snd)
    (ha : ∀ n, (sourceRealAction (by simp) (by norm_num) φ.val φ.property n).re =
      (sourceRealAction (by simp) (by norm_num) ψ.val ψ.property n).re)
    (hpos : ∀ n : ℤ, 0 < n →
      (D.hilbertRealHomeomorph φ).1 n = (D.hilbertRealHomeomorph ψ).1 n ∧
        (D.hilbertRealHomeomorph φ).2 n = (D.hilbertRealHomeomorph ψ).2 n) :
    ψ = φ ∨ ψ = D.hilbertActionRotation φ 0 Real.pi := by
  have hφP : realSourceComponentSwap φ = φ := Subtype.ext ((sourceComponentSwap_eq_self_iff _).mpr hφ)
  have hψP : realSourceComponentSwap ψ = ψ := Subtype.ext ((sourceComponentSwap_eq_self_iff _).mpr hψ)
  have hφQ : D.coordinateComponentSwap (D.hilbertRealHomeomorph φ) = D.hilbertRealHomeomorph φ := by
    rw [coordinateComponentSwap,Homeomorph.symm_apply_apply,hφP]
  have hψQ : D.coordinateComponentSwap (D.hilbertRealHomeomorph ψ) = D.hilbertRealHomeomorph ψ := by
    rw [coordinateComponentSwap,Homeomorph.symm_apply_apply,hψP]
  have hact (n : ℤ) : RealCoeff.pairAction (D.hilbertRealHomeomorph φ) n =
      RealCoeff.pairAction (D.hilbertRealHomeomorph ψ) n := by
    change RealCoeff.pairAction (sourceRealBirkhoffMap (by simp) (by norm_num) s φ) n =
      RealCoeff.pairAction (sourceRealBirkhoffMap (by simp) (by norm_num) s ψ) n
    rw [D.real_pairAction_eq,D.real_pairAction_eq,ha n]
  rcases RealCoeff.eq_or_central_halfTurn_of_reflection_fixed (by norm_num) D.coordinateComponentSwap
    D.continuous_coordinateComponentSwap D.coordinateComponentSwap_rotation
    (D.hilbertRealHomeomorph φ) (D.hilbertRealHomeomorph ψ) hφQ hψQ hact hpos with h | h
  · exact Or.inl (D.hilbertRealHomeomorph.injective h)
  · right
    apply D.hilbertRealHomeomorph.injective
    rw [D.hilbertRealHomeomorph_actionRotation]
    exact h

/-- A closed central action removes the sole possible half-turn
ambiguity, globally on the original real L2 diagonal. -/
theorem diagonal_eq_of_positive_coordinates_of_central_action_zero
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ ψ : realTypeSourceSubmodule 2) (hφ : φ.val.fst = φ.val.snd) (hψ : ψ.val.fst = ψ.val.snd)
    (ha : ∀ n, (sourceRealAction (by simp) (by norm_num) φ.val φ.property n).re =
      (sourceRealAction (by simp) (by norm_num) ψ.val ψ.property n).re)
    (hpos : ∀ n : ℤ, 0 < n →
      (D.hilbertRealHomeomorph φ).1 n = (D.hilbertRealHomeomorph ψ).1 n ∧
        (D.hilbertRealHomeomorph φ).2 n = (D.hilbertRealHomeomorph ψ).2 n)
    (h0 : (sourceRealAction (by simp) (by norm_num) φ.val φ.property 0).re = 0) : ψ = φ := by
  rcases D.diagonal_eq_or_central_halfTurn φ ψ hφ hψ ha hpos with h | h
  · exact h
  · rw [h]
    apply D.hilbertRealHomeomorph.injective
    rw [D.hilbertRealHomeomorph_actionRotation]
    apply RealCoeff.actionRotation_eq_self_of_action_zero
    change RealCoeff.pairAction (sourceRealBirkhoffMap (by simp) (by norm_num) s φ) 0 = 0
    rw [D.real_pairAction_eq,h0]

end NLS.ZakharovShabat.SourceBirkhoffMapComplexData
