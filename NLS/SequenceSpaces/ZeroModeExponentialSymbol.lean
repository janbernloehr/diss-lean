import NLS.SequenceSpaces.WeightedSymbolGauge
import NLS.SequenceSpaces.WeightedZeroMode

/-! Bounded exponential symbols preserve the exact zero-mode kernel
and restrict to genuine continuous linear equivalences on that kernel. -/
noncomputable section
open scoped ENNReal
namespace NLS.WeightedCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem exponentialSymbolEquiv_map_zeroMode (w : Weight) (b : Coeff ⊤) :
    (zeroModeSubmodule w p).map (exponentialSymbolEquiv w b).toLinearEquiv.toLinearMap =
      zeroModeSubmodule w p := by
  ext a
  constructor
  · rintro ⟨c,hc,rfl⟩
    change c.val 0 = 0 at hc
    change (exponentialSymbolEquiv w b c).val 0 = 0
    rw [exponentialSymbolEquiv_apply,hc,mul_zero]
  · intro ha
    change a.val 0 = 0 at ha
    refine ⟨(exponentialSymbolEquiv w b).symm a,?_,(exponentialSymbolEquiv w b).apply_symm_apply a⟩
    change ((exponentialSymbolEquiv w b).symm a).val 0 = 0
    rw [exponentialSymbolEquiv_symm_apply,ha,mul_zero]

def zeroModeExponentialSymbolEquiv (w : Weight) (b : Coeff ⊤) :
    zeroModeSubmodule w p ≃L[ℂ] zeroModeSubmodule w p :=
  (exponentialSymbolEquiv w b).ofSubmodules _ _ (exponentialSymbolEquiv_map_zeroMode w b)

theorem zeroModeExponentialSymbolEquiv_coe (w : Weight) (b : Coeff ⊤)
    (a : zeroModeSubmodule w p) :
    (zeroModeExponentialSymbolEquiv w b a).val = exponentialSymbolEquiv w b a.val := rfl

theorem zeroModeProjection_exponentialSymbolEquiv (w : Weight) (b : Coeff ⊤)
    (a : WeightedCoeff w p) :
    zeroModeProjection w (exponentialSymbolEquiv w b a) =
      zeroModeExponentialSymbolEquiv w b (zeroModeProjection w a) := by
  apply Subtype.ext
  apply Subtype.ext
  funext k
  change (eraseZeroModeCLM w (exponentialSymbolEquiv w b a)).val k =
    (exponentialSymbolEquiv w b (eraseZeroModeCLM w a)).val k
  rw [eraseZeroModeCLM_apply,exponentialSymbolEquiv_apply,exponentialSymbolEquiv_apply,
    eraseZeroModeCLM_apply]
  split_ifs <;> simp only [mul_zero]

end NLS.WeightedCoeff
