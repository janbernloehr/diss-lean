import NLS.SequenceSpaces.RealPairedActionRotation
import NLS.ZakharovShabat.SourceHilbertActionRotation
import NLS.ZakharovShabat.SourceComponentSwapPoisson
import NLS.FunctionalAnalysis.AutonomousODEUniqueness

/-! # Complete paired original NLS action flows

The exact inverse Jacobian identifies opposite coordinate rotations with
the actual Hamiltonian field of I_k-I_l. Analytic ODE uniqueness makes
the resulting flow independent of the chosen normalized Birkhoff family.
-/
noncomputable section
open Set Complex Filter Topology NLS.Poisson
namespace NLS.ZakharovShabat

def sourceActionDifferenceVector (k l : ℤ) (φ : CoeffPair 2) : CoeffPair 2 :=
  sourceHamiltonianVector le_rfl (sourceComplexAction (by simp) (by norm_num) k) φ-
    sourceHamiltonianVector le_rfl (sourceComplexAction (by simp) (by norm_num) l) φ

theorem analyticAt_sourceActionDifferenceVector (k l : ℤ) (φ : realTypeSourceSubmodule 2) :
    AnalyticAt ℂ (sourceActionDifferenceVector k l) φ.val := by
  have hk := analyticAt_sourceComplexAction_of_realType (by simp) (by norm_num) k φ.val φ.property
  have hl := analyticAt_sourceComplexAction_of_realType (by simp) (by norm_num) l φ.val φ.property
  exact (((sourceHamiltonianDirection le_rfl).analyticAt _).comp hk.fderiv).sub
    (((sourceHamiltonianDirection le_rfl).analyticAt _).comp hl.fderiv)

namespace SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)} {s : (k : ℤ) → CoeffPair 2 → DeletedCoeff 2 k}

def hilbertPairedActionFlow
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (k l : ℤ) (t : ℝ) : realTypeSourceSubmodule 2 :=
  D.hilbertRealHomeomorph.symm (RealCoeff.pairedActionRotation (D.hilbertRealHomeomorph φ) k l t)

@[simp] theorem hilbertRealHomeomorph_pairedActionFlow
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (k l : ℤ) (t : ℝ) :
    D.hilbertRealHomeomorph (D.hilbertPairedActionFlow φ k l t) =
      RealCoeff.pairedActionRotation (D.hilbertRealHomeomorph φ) k l t :=
  D.hilbertRealHomeomorph.apply_symm_apply _

@[simp] theorem hilbertPairedActionFlow_zero
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (k l : ℤ) : D.hilbertPairedActionFlow φ k l 0 = φ := by
  simp only [hilbertPairedActionFlow,RealCoeff.pairedActionRotation_zero]
  exact D.hilbertRealHomeomorph.symm_apply_apply φ

theorem hilbertPairedActionFlow_eq_rotations
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (k l : ℤ) (t : ℝ) :
    D.hilbertPairedActionFlow φ k l t =
      D.hilbertActionRotation (D.hilbertActionRotation φ k t) l (-t) := by
  apply D.hilbertRealHomeomorph.injective
  simp only [hilbertRealHomeomorph_pairedActionFlow,hilbertRealHomeomorph_actionRotation,
    RealCoeff.pairedActionRotation]

theorem hasDerivAt_hilbertPairedActionFlow
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (k l : ℤ) (t : ℝ) :
    HasDerivAt (fun r => (D.hilbertPairedActionFlow φ k l r).val)
      (sourceActionDifferenceVector k l (D.hilbertPairedActionFlow φ k l t).val) t := by
  let z := D.hilbertRealHomeomorph φ
  let χ := D.hilbertPairedActionFlow φ k l t
  have hd := (D.hilbertRealHomeomorph_symm_hasStrictFDerivAt
    (RealCoeff.pairedActionRotation z k l t)).hasFDerivAt.comp_hasDerivAt t
      (RealCoeff.hasDerivAt_pairedActionRotation z k l t)
  have hc := (realTypeSourceSubmodule 2).subtypeL.hasFDerivAt.comp_hasDerivAt t hd
  change HasDerivAt (fun r => (D.hilbertPairedActionFlow φ k l r).val)
    ((D.realJacobianEquivAll χ).symm
      (RealCoeff.actionRotationVector (RealCoeff.pairedActionRotation z k l t) k-
        RealCoeff.actionRotationVector (RealCoeff.pairedActionRotation z k l t) l)).val t at hc
  have he : RealCoeff.pairedActionRotation z k l t = D.hilbertRealHomeomorph χ :=
    (D.hilbertRealHomeomorph_pairedActionFlow φ k l t).symm
  rw [he,map_sub] at hc
  change HasDerivAt (fun r => (D.hilbertPairedActionFlow φ k l r).val)
    ((D.hilbertActionRotationVector χ k).val-(D.hilbertActionRotationVector χ l).val) t at hc
  rw [D.hilbertActionRotationVector_eq_actionHamiltonian,D.hilbertActionRotationVector_eq_actionHamiltonian] at hc
  exact hc

/-- Uniqueness holds against arbitrary complex source curves with the
same real initial value, not just curves constructed in coordinates. -/
theorem hilbertPairedActionFlow_unique
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (k l : ℤ) (g : ℝ → CoeffPair 2)
    (hzero : g 0 = φ.val)
    (hg : ∀ t, HasDerivAt g (sourceActionDifferenceVector k l (g t)) t) :
    g = fun t => (D.hilbertPairedActionFlow φ k l t).val := by
  have he : EqOn (fun t => (D.hilbertPairedActionFlow φ k l t).val) g univ := by
    apply NLS.FunctionalAnalysis.eqOn_of_autonomous_hasDerivAt isOpen_univ isPreconnected_univ
      (v := sourceActionDifferenceVector k l) (t₀ := 0)
    · intro t _
      exact ((analyticAt_sourceActionDifferenceVector k l (D.hilbertPairedActionFlow φ k l t)).restrictScalars
        (𝕜 := ℝ)).contDiffAt
    · exact fun t _ => D.hasDerivAt_hilbertPairedActionFlow φ k l t
    · exact fun t _ => hg t
    · exact mem_univ 0
    · simpa only [hilbertPairedActionFlow_zero] using hzero.symm
  exact funext (fun t => (he (mem_univ t)).symm)

theorem discriminant_hilbertPairedActionFlow
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (k l : ℤ) (t : ℝ) :
    canonicalDiscriminant (by simp) (periodOnePotential (D.hilbertPairedActionFlow φ k l t).val) =
      canonicalDiscriminant (by simp) (periodOnePotential φ.val) := by
  rw [D.hilbertPairedActionFlow_eq_rotations,D.discriminant_hilbertActionRotation,
    D.discriminant_hilbertActionRotation]

theorem continuous_hilbertPairedActionFlow
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s) (k l : ℤ) :
    Continuous (fun x : ℝ × realTypeSourceSubmodule 2 => D.hilbertPairedActionFlow x.2 k l x.1) := by
  have hpair : Continuous (fun x : ℝ × realTypeSourceSubmodule 2 =>
      (x.1,D.hilbertRealHomeomorph x.2)) :=
    continuous_fst.prodMk (D.hilbertRealHomeomorph.continuous.comp continuous_snd)
  have hrot := (RealCoeff.continuous_pairedActionRotation (p := 2) k l).comp hpair
  exact D.hilbertRealHomeomorph.symm.continuous.comp hrot

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
