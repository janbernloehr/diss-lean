import NLS.ZakharovShabat.SourcePairedActionFlow
import NLS.SequenceSpaces.RealPairedActionRotationProperties

/-! # The diagonal-preserving complete action group

Component exchange reverses each action field and reflects its signed
index. The difference I_n-I_-n is therefore equivariant. Actual ODE
uniqueness proves covariance of its complete paired flow and preservation
of the original equal-component real diagonal.
-/
noncomputable section
open Set Complex Filter Topology NLS.Poisson
namespace NLS.ZakharovShabat

theorem sourceActionDifferenceVector_componentSwap (n : ℤ) (φ : realTypeSourceSubmodule 2) :
    sourceComponentSwap (sourceActionDifferenceVector n (-n) φ.val) =
      sourceActionDifferenceVector n (-n) (sourceComponentSwap φ.val) := by
  rw [sourceActionDifferenceVector,map_sub,
    sourceActionHamiltonianVector_componentSwap (by simp) (by norm_num) le_rfl φ n,
    sourceActionHamiltonianVector_componentSwap (by simp) (by norm_num) le_rfl φ (-n),neg_neg]
  unfold sourceActionDifferenceVector
  abel

namespace SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)} {s : (k : ℤ) → CoeffPair 2 → DeletedCoeff 2 k}

/-- Two normalized coordinate constructions lift exactly the same
physical action-difference field. -/
theorem hilbertPairedActionFlow_independent
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    {W₀' B' W' : Set (CoeffPair 2)} {s' : (k : ℤ) → CoeffPair 2 → DeletedCoeff 2 k}
    (E : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀' B' W' s')
    (φ : realTypeSourceSubmodule 2) (k l : ℤ) (t : ℝ) :
    D.hilbertPairedActionFlow φ k l t = E.hilbertPairedActionFlow φ k l t := by
  apply Subtype.ext
  exact (congrFun (D.hilbertPairedActionFlow_unique φ k l
    (fun r => (E.hilbertPairedActionFlow φ k l r).val)
    (by rw [E.hilbertPairedActionFlow_zero])
    (fun r => E.hasDerivAt_hilbertPairedActionFlow φ k l r)) t).symm

theorem hilbertPairedActionFlow_componentSwap
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (n : ℤ) (t : ℝ) :
    sourceComponentSwap (D.hilbertPairedActionFlow φ n (-n) t).val =
      (D.hilbertPairedActionFlow (realSourceComponentSwap φ) n (-n) t).val := by
  have hd (r : ℝ) : HasDerivAt
      (fun r => sourceComponentSwap (D.hilbertPairedActionFlow φ n (-n) r).val)
      (sourceActionDifferenceVector n (-n)
        (sourceComponentSwap (D.hilbertPairedActionFlow φ n (-n) r).val)) r := by
    have h := ((sourceComponentSwap (p := 2)).toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt r
      (D.hasDerivAt_hilbertPairedActionFlow φ n (-n) r)
    change HasDerivAt (fun r => sourceComponentSwap (D.hilbertPairedActionFlow φ n (-n) r).val)
      (sourceComponentSwap (sourceActionDifferenceVector n (-n)
        (D.hilbertPairedActionFlow φ n (-n) r).val)) r at h
    rw [sourceActionDifferenceVector_componentSwap] at h
    exact h
  exact congrFun (D.hilbertPairedActionFlow_unique (realSourceComponentSwap φ) n (-n)
    (fun r => sourceComponentSwap (D.hilbertPairedActionFlow φ n (-n) r).val)
    (by rw [D.hilbertPairedActionFlow_zero]; rfl) hd) t

/-- Equal original components stay equal for every real time, with no
finite-gap or open-action condition. -/
theorem hilbertPairedActionFlow_diagonal
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (hφ : φ.val.fst = φ.val.snd) (n : ℤ) (t : ℝ) :
    (D.hilbertPairedActionFlow φ n (-n) t).val.fst =
      (D.hilbertPairedActionFlow φ n (-n) t).val.snd := by
  have hfixed : realSourceComponentSwap φ = φ := Subtype.ext ((sourceComponentSwap_eq_self_iff _).mpr hφ)
  apply (sourceComponentSwap_eq_self_iff _).mp
  rw [D.hilbertPairedActionFlow_componentSwap,hfixed]

theorem hilbertPairedActionFlow_add
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (k l : ℤ) (t u : ℝ) :
    D.hilbertPairedActionFlow (D.hilbertPairedActionFlow φ k l t) k l u =
      D.hilbertPairedActionFlow φ k l (t+u) := by
  apply D.hilbertRealHomeomorph.injective
  simp only [hilbertRealHomeomorph_pairedActionFlow,RealCoeff.pairedActionRotation_add]

theorem hilbertPairedActionFlow_comm
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (k l m n : ℤ) (t u : ℝ) :
    D.hilbertPairedActionFlow (D.hilbertPairedActionFlow φ k l t) m n u =
      D.hilbertPairedActionFlow (D.hilbertPairedActionFlow φ m n u) k l t := by
  apply D.hilbertRealHomeomorph.injective
  simp only [hilbertRealHomeomorph_pairedActionFlow,RealCoeff.pairedActionRotation_comm]

theorem hilbertPairedActionFlow_periodic
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (k l : ℤ) :
    Function.Periodic (D.hilbertPairedActionFlow φ k l) (2*Real.pi) := by
  intro t
  apply D.hilbertRealHomeomorph.injective
  simp only [hilbertRealHomeomorph_pairedActionFlow,
    RealCoeff.pairedActionRotation_periodic (D.hilbertRealHomeomorph φ) k l t]

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
