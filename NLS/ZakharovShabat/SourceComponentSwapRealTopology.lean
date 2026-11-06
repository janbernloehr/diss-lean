import NLS.ZakharovShabat.SourceComponentSwap

/-! # Bounded unsigned exchange on the original real source -/
noncomputable section
set_option autoImplicit false
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The original real component exchange as a bounded real linear map. -/
def realSourceComponentSwapCLM : realTypeSourceSubmodule p →L[ℝ] realTypeSourceSubmodule p :=
  (((sourceComponentSwap (p := p)).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).comp
    (realTypeSourceSubmodule p).subtypeL).codRestrict (realTypeSourceSubmodule p)
      (fun φ => sourceComponentSwap_realType φ.val φ.property)

@[simp] theorem realSourceComponentSwapCLM_apply (φ : realTypeSourceSubmodule p) :
    realSourceComponentSwapCLM φ = realSourceComponentSwap φ := rfl

theorem continuous_realSourceComponentSwap :
    Continuous (realSourceComponentSwap (p := p)) := realSourceComponentSwapCLM.continuous

end NLS.ZakharovShabat
