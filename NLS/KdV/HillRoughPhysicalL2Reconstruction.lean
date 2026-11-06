import NLS.KdV.HillUnitRealSourceCoordinates
import NLS.KdV.HillHminusOriginalSourceAdapter
import NLS.KdV.HillOriginalMeanZeroSpectralDerivative

/-! # Literal physical L2 reconstruction of a regular rough source

Raw L2 membership of a real mean-zero H-minus-one source gives an ORIGINAL
real mean-zero physical potential with exactly the same rough inclusion.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
namespace NLS.KdV

theorem exists_original_physical_meanZero_of_real_hminus_l2
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (hm : q.val 0=0)
    (hL2 : Memℓp q.val 2) :
    ∃ p : hillRealMeanZeroSourceSubmodule, hillOriginalHminusSource p.val.val=q := by
  let u : Coeff 2 := ⟨q.val,hL2⟩
  have hu : periodOneL2Conjugation u=u := (periodOneL2Conjugation_fixed_iff _).mpr hr
  let P := hillRealWeightedEmbedding SpectralWeight.one (hillUnitRealSourceLift u hu)
  have hcoeff : SpectralWeight.one.toCoeff P.val=Coeff.periodDouble u := by
    rw [hillRealWeightedEmbedding_toCoeff,hillUnitRealSourceLift_toCoeff]
  have hs : hillOriginalHminusSource P.val=q := by
    apply Subtype.ext
    funext j
    rw [hillOriginalHminusSource_apply]
    have hc := congrArg (fun a : Coeff 2 => a (2*j)) hcoeff
    simpa only [SpectralWeight.toCoeff_apply,Coeff.periodDouble_even] using hc
  have hmean : P.val.val 0=0 := by
    have hh := congrArg (fun a : PeriodOneHminusOne => a.val 0) hs
    rw [hillOriginalHminusSource_apply,mul_zero,hm] at hh
    exact hh
  exact ⟨⟨⟨P.val,P.property⟩,(mem_hillRealMeanZeroSourceSubmodule _).mpr hmean⟩,hs⟩

end NLS.KdV
