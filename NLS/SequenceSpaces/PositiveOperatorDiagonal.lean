import NLS.SequenceSpaces.PositiveInsertion
import NLS.SequenceSpaces.OperatorDiagonal

/-! Canonical diagonal extraction on positive-index l2, using the
existing signed-space multiplier and isometric positive insertion. -/
noncomputable section
open Set Complex
open scoped ENNReal Classical
namespace NLS.LpSequence

theorem positiveRestriction_single (m : ℕ+) (z : ℂ) :
    positiveRestriction (lp.single 2 ((m:ℕ):ℤ) z) = lp.single 2 m z := by
  ext r
  change (lp.single 2 ((m:ℕ):ℤ) z : Coeff 2) ((r:ℕ):ℤ) =
    (lp.single 2 m z : lp (fun _ : ℕ+ => ℂ) 2) r
  have he : ((r:ℕ):ℤ) = ((m:ℕ):ℤ) ↔ r = m :=
    ⟨fun h => Subtype.ext (Int.ofNat.inj h),fun h => by rw [h]⟩
  simp only [lp.single_apply,Pi.single_apply,he]

def positiveLiftOperator (T : lp (fun _ : ℕ+ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ+ => ℂ) 2) :
    Coeff 2 →L[ℂ] Coeff 2 :=
  positiveInsertIsometry.toContinuousLinearMap.comp (T.comp positiveRestrictionCLM)

def positiveOperatorDiagonal (T : lp (fun _ : ℕ+ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ+ => ℂ) 2) :
    lp (fun _ : ℕ+ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ+ => ℂ) 2 :=
  positiveRestrictionCLM.comp ((Coeff.multiplierCLM (Coeff.operatorDiagonalSymbol (positiveLiftOperator T))).comp
    positiveInsertIsometry.toContinuousLinearMap)

theorem positiveOperatorDiagonal_apply
    (T : lp (fun _ : ℕ+ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ+ => ℂ) 2)
    (a : lp (fun _ : ℕ+ => ℂ) 2) (m : ℕ+) :
    positiveOperatorDiagonal T a m = T (lp.single 2 m 1) m*a m := by
  change (Coeff.multiplierCLM (Coeff.operatorDiagonalSymbol (positiveLiftOperator T))
    (positiveInsert a)) ((m:ℕ):ℤ) = _
  rw [Coeff.multiplierCLM_apply,Coeff.multiplier_apply,Coeff.operatorDiagonalSymbol_apply]
  change positiveInsert (T (positiveRestriction (lp.single 2 ((m:ℕ):ℤ) 1))) ((m:ℕ):ℤ)*
    positiveInsert a ((m:ℕ):ℤ) = _
  rw [positiveRestriction_single,positiveInsert_apply,positiveInsert_apply]

def positiveOperatorOffDiagonal (T : lp (fun _ : ℕ+ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ+ => ℂ) 2) :
    lp (fun _ : ℕ+ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ+ => ℂ) 2 := T-positiveOperatorDiagonal T

theorem positiveOperatorOffDiagonal_entry
    (T : lp (fun _ : ℕ+ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ+ => ℂ) 2) (m r : ℕ+) :
    positiveOperatorOffDiagonal T (lp.single 2 r 1) m = if m = r then 0 else T (lp.single 2 r 1) m := by
  change T (lp.single 2 r 1) m-positiveOperatorDiagonal T (lp.single 2 r 1) m = _
  rw [positiveOperatorDiagonal_apply]
  by_cases hmr : m = r <;> simp [lp.single_apply,hmr]

theorem positiveOperator_eq_diagonal_add_offDiagonal
    (T : lp (fun _ : ℕ+ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ+ => ℂ) 2) :
    T = positiveOperatorDiagonal T+positiveOperatorOffDiagonal T := by
  unfold positiveOperatorOffDiagonal
  abel

end NLS.LpSequence
