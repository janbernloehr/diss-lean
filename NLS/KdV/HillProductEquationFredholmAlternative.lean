import NLS.KdV.HillProductEquationInvertibleDiagonal
import NLS.FunctionalAnalysis.CompactPerturbationEquiv

/-! At every actual real source, full period-Jacobian invertibility
reduces to kernel injectivity. The latter is an explicit unproved premise. -/
noncomputable section
open Complex
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem sequenceJacobian_actual_real_bijective_of_injective (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) (n : ℕ+)
    (hinj : Function.Injective (P.sequenceJacobian n (hillHminusPsiZeroDisplacement n ⟨q,hr⟩,q))) :
    Function.Bijective (P.sequenceJacobian n (hillHminusPsiZeroDisplacement n ⟨q,hr⟩,q)) := by
  obtain ⟨_,_,_,D,K,hK,he,_,_,_⟩ := P.exists_actual_real_diagonal_equiv q hq hr n
  apply NLS.CompactSpectrum.bijective_of_injective_compact_sub_equiv _ D _ hinj
  rw [he,add_sub_cancel_left]
  exact hK

end NLS.KdV.HillProductEquationPatch
