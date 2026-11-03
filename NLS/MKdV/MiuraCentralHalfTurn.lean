import NLS.MKdV.MiuraNLSActionFiberMean
import NLS.ZakharovShabat.SourceCentralHalfTurn

/-! # The actual central NLS half-turn on the physical scalar L2 diagonal -/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem continuous_miuraRealDiagonalL2Source : Continuous miuraRealDiagonalL2Source :=
  (scalarL2Diagonal.continuous.comp continuous_subtype_val).subtype_mk _

def miuraCentralHalfTurnSource (a : MiuraRealL2) : realTypeSourceSubmodule 2 :=
  miuraActionFlowFamily.data.hilbertActionRotation (miuraRealDiagonalL2Source a) 0 Real.pi

theorem miuraCentralHalfTurnSource_diagonal (a : MiuraRealL2) :
    (miuraCentralHalfTurnSource a).val.fst = (miuraCentralHalfTurnSource a).val.snd :=
  miuraActionFlowFamily.data.hilbertCentralHalfTurn_diagonal (miuraRealDiagonalL2Source a)
    ((scalarL2Diagonal_fst a.val).trans (scalarL2Diagonal_snd a.val).symm)

def miuraCentralHalfTurn (a : MiuraRealL2) : MiuraRealL2 :=
  ⟨(miuraCentralHalfTurnSource a).val.fst,by
    intro j
    exact (congrArg (fun c : Coeff 2 => c j) (miuraCentralHalfTurnSource_diagonal a)).trans ((miuraCentralHalfTurnSource a).property j)⟩

theorem miuraCentralHalfTurn_source (a : MiuraRealL2) :
    miuraRealDiagonalL2Source (miuraCentralHalfTurn a) = miuraCentralHalfTurnSource a := by
  apply Subtype.ext
  apply (CoeffPair.toMax 2).injective
  apply Prod.ext
  · exact scalarL2Diagonal_fst _
  · exact (scalarL2Diagonal_snd _).trans (miuraCentralHalfTurnSource_diagonal a)

theorem continuous_miuraCentralHalfTurn : Continuous miuraCentralHalfTurn := by
  have hs : Continuous miuraCentralHalfTurnSource :=
    (miuraActionFlowFamily.data.continuous_hilbertActionRotation_initial 0 Real.pi).comp
      continuous_miuraRealDiagonalL2Source
  exact ((continuous_fst.comp (CoeffPair.toMax 2).continuous).comp
    (continuous_subtype_val.comp hs)).subtype_mk _

theorem miuraCentralHalfTurn_NLS_actionSequence (a : MiuraRealL2) :
    miuraOriginalNLSActionSequence (miuraCentralHalfTurn a).val = miuraOriginalNLSActionSequence a.val := by
  have hsource := congrArg Subtype.val (miuraCentralHalfTurn_source a)
  change scalarL2Diagonal (miuraCentralHalfTurn a).val = (miuraCentralHalfTurnSource a).val at hsource
  change sourceHilbertActionSequence miuraActionFlowFamily.psi (scalarL2Diagonal (miuraCentralHalfTurn a).val) = _
  rw [hsource]
  exact miuraActionFlowFamily.data.hilbert_actionSequence_actionRotation (miuraRealDiagonalL2Source a) 0 Real.pi

theorem miuraCentralHalfTurn_physical_actionSequence (a : MiuraRealL2) :
    miuraL2ActionSequence (miuraCentralHalfTurn a).val = miuraL2ActionSequence a.val :=
  miuraL2ActionSequence_eq_of_NLS_actions_eq _ _ (miuraCentralHalfTurn_NLS_actionSequence a)

theorem miuraCentralHalfTurn_mean_square (a : MiuraRealL2) :
    ((miuraCentralHalfTurn a).val 0)^2 = (a.val 0)^2 :=
  miuraMean_square_eq_of_NLS_actions_eq a _ (miuraCentralHalfTurn_NLS_actionSequence a).symm

theorem miuraCentralHalfTurn_eq_self_iff_central_action_zero (a : MiuraRealL2) :
    miuraCentralHalfTurn a = a ↔ miuraOriginalNLSActionSequence a.val 0 = 0 := by
  have hcoord := miuraActionFlowFamily.data.hilbertActionRotation_pi_eq_self_iff_action_zero
    (miuraRealDiagonalL2Source a) 0
  change miuraCentralHalfTurnSource a = miuraRealDiagonalL2Source a ↔ _ at hcoord
  rw [← miuraCentralHalfTurn_source a] at hcoord
  rw [miuraOriginalNLSActionSequence_apply a.val (real_mem_miuraOriginalNLSActionDomain a.val a.property)]
  constructor
  · intro h; exact hcoord.mp (congrArg miuraRealDiagonalL2Source h)
  · intro h
    have hs := hcoord.mpr h
    apply Subtype.ext
    have he := congrArg (fun φ : realTypeSourceSubmodule 2 => φ.val.fst) hs
    change (scalarL2Diagonal (miuraCentralHalfTurn a).val).fst = (scalarL2Diagonal a.val).fst at he
    simpa only [scalarL2Diagonal_fst] using he

end NLS.MKdV
