import NLS.ZakharovShabat.SourceComponentSwapRealTopology
import NLS.ZakharovShabat.SourcePairedActionFlowDiagonal

/-! # Component exchange conjugates each complete action flow

The original component swap reverses the Poisson sign and reflects the
action index. ODE uniqueness therefore reverses time as well, at every
real source and every time, including closed actions.
-/
noncomputable section
open Set Complex Filter Topology NLS.Poisson
namespace NLS.ZakharovShabat

theorem analyticAt_sourceActionHamiltonianVector (k : ℤ) (φ : realTypeSourceSubmodule 2) :
    AnalyticAt ℂ (sourceHamiltonianVector le_rfl (sourceComplexAction (by simp) (by norm_num) k)) φ.val := by
  have hk := analyticAt_sourceComplexAction_of_realType (by simp) (by norm_num) k φ.val φ.property
  exact ((sourceHamiltonianDirection le_rfl).analyticAt _).comp hk.fderiv

namespace SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)} {s : (k : ℤ) → CoeffPair 2 → DeletedCoeff 2 k}

theorem hilbertActionRotation_unique
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (k : ℤ) (g : ℝ → CoeffPair 2)
    (hzero : g 0 = φ.val)
    (hg : ∀ t, HasDerivAt g
      (sourceHamiltonianVector le_rfl (sourceComplexAction (by simp) (by norm_num) k) (g t)) t) :
    g = fun t => (D.hilbertActionRotation φ k t).val := by
  have he : EqOn (fun t => (D.hilbertActionRotation φ k t).val) g univ := by
    apply NLS.FunctionalAnalysis.eqOn_of_autonomous_hasDerivAt isOpen_univ isPreconnected_univ
      (v := sourceHamiltonianVector le_rfl (sourceComplexAction (by simp) (by norm_num) k)) (t₀ := 0)
    · intro t _
      exact ((analyticAt_sourceActionHamiltonianVector k (D.hilbertActionRotation φ k t)).restrictScalars
        (𝕜 := ℝ)).contDiffAt
    · exact fun t _ => D.hasDerivAt_hilbertActionRotation_actionHamiltonian φ k t
    · exact fun t _ => hg t
    · exact mem_univ 0
    · simpa only [hilbertActionRotation_zero] using hzero.symm
  exact funext (fun t => (he (mem_univ t)).symm)

/-- Exact complete source action-flow covariance, with both reflected
index and reversed time. -/
theorem hilbertActionRotation_componentSwap
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (k : ℤ) (t : ℝ) :
    realSourceComponentSwap (D.hilbertActionRotation φ k t) =
      D.hilbertActionRotation (realSourceComponentSwap φ) (-k) (-t) := by
  have hd (r : ℝ) : HasDerivAt
      (fun r => sourceComponentSwap (D.hilbertActionRotation φ k (-r)).val)
      (sourceHamiltonianVector le_rfl (sourceComplexAction (by simp) (by norm_num) (-k))
        (sourceComponentSwap (D.hilbertActionRotation φ k (-r)).val)) r := by
    have hneg : HasDerivAt (fun u : ℝ => -u) (-1 : ℝ) r := by
      simpa only [Function.comp_def] using! (hasDerivAt_id r).neg
    have ht := (D.hasDerivAt_hilbertActionRotation_actionHamiltonian φ k (-r)).scomp r hneg
    have h := ((sourceComponentSwap (p := 2)).toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt r ht
    change HasDerivAt (fun r => sourceComponentSwap (D.hilbertActionRotation φ k (-r)).val)
      (sourceComponentSwap ((-1 : ℝ) •
        sourceHamiltonianVector le_rfl (sourceComplexAction (by simp) (by norm_num) k)
          (D.hilbertActionRotation φ k (-r)).val)) r at h
    rw [neg_one_smul,map_neg,sourceActionHamiltonianVector_componentSwap (by simp) (by norm_num)
      le_rfl (D.hilbertActionRotation φ k (-r)) k,neg_neg] at h
    exact h
  have he := congrFun (D.hilbertActionRotation_unique (realSourceComponentSwap φ) (-k)
    (fun r => sourceComponentSwap (D.hilbertActionRotation φ k (-r)).val)
    (by simp only [neg_zero,hilbertActionRotation_zero]; rfl) hd) (-t)
  apply Subtype.ext
  simpa only [neg_neg,realSourceComponentSwap_val] using he

def coordinateComponentSwap
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (z : RealCoeff 2 × RealCoeff 2) : RealCoeff 2 × RealCoeff 2 :=
  D.hilbertRealHomeomorph (realSourceComponentSwap (D.hilbertRealHomeomorph.symm z))

theorem continuous_coordinateComponentSwap
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s) : Continuous D.coordinateComponentSwap :=
  D.hilbertRealHomeomorph.continuous.comp
    (continuous_realSourceComponentSwap.comp D.hilbertRealHomeomorph.symm.continuous)

theorem coordinateComponentSwap_rotation
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (z : RealCoeff 2 × RealCoeff 2) (k : ℤ) (t : ℝ) :
    D.coordinateComponentSwap (RealCoeff.actionRotation z k t) =
      RealCoeff.actionRotation (D.coordinateComponentSwap z) (-k) (-t) := by
  have h := congrArg D.hilbertRealHomeomorph
    (D.hilbertActionRotation_componentSwap (D.hilbertRealHomeomorph.symm z) k t)
  simpa only [coordinateComponentSwap,hilbertActionRotation,Homeomorph.apply_symm_apply] using h

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
