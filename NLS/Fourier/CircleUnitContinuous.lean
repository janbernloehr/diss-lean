import NLS.Fourier.UnitIntervalContinuousLp
import NLS.Fourier.CircleContinuousLp

/-! Restriction of the identical continuous period-two representative to
the closed unit interval, with the exact supremum-norm bound one. -/
noncomputable section
open Set
namespace NLS.Fourier

/-- Physical restriction to the original closed unit interval. -/
def circleUnitContinuousRestriction :
    C(AddCircle (2:ℝ),ℂ) →L[ℂ] C(Icc (0:ℝ) 1,ℂ) :=
  ContinuousMap.compCLM ℂ ℂ
    (⟨fun x : Icc (0:ℝ) 1 => (x.val : AddCircle (2:ℝ)),
      (AddCircle.continuous_mk' (2:ℝ)).comp continuous_subtype_val⟩ :
      C(Icc (0:ℝ) 1,AddCircle (2:ℝ)))

/-- No representative or boundary point changes under restriction. -/
theorem circleUnitContinuousRestriction_apply (F : C(AddCircle (2:ℝ),ℂ))
    (x : Icc (0:ℝ) 1) :
    circleUnitContinuousRestriction F x = F (x.val : AddCircle (2:ℝ)) := rfl

/-- The interval has the same physical values, with a smaller supremum. -/
theorem norm_circleUnitContinuousRestriction_le (F : C(AddCircle (2:ℝ),ℂ)) :
    ‖circleUnitContinuousRestriction F‖ ≤ ‖F‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg F)).mpr
  intro x
  exact F.norm_coe_le_norm _

end NLS.Fourier
