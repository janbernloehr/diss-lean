import NLS.MKdV.SobolevQuasiHill

/-! The bounded original period-one H1 curve map, separated from primitive
and hierarchy comparisons. -/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory NLS.LinearVolterra NLS.Fourier
open NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.MKdV

/-- The physical period-one representative is a bounded complex-linear
map in the original H¹ norm. -/
def periodOneMiuraCurveCLM : ScalarDomain 2 →L[ℂ] Curve ℂ :=
  (ContinuousMap.compCLM ℂ ℂ
    (⟨fun t : Icc (0 : ℝ) 1 => (t.val : AddCircle (2 : ℝ)),
      (AddCircle.continuous_mk' (2 : ℝ)).comp continuous_subtype_val⟩ :
        C(Icc (0 : ℝ) 1,AddCircle (2 : ℝ)))).comp periodOneSobolevSynthesis

@[simp] theorem periodOneMiuraCurveCLM_apply (a : ScalarDomain 2) :
    periodOneMiuraCurveCLM a = periodOneMiuraCurve a := by
  apply ContinuousMap.ext
  intro t
  exact (periodOneMiuraCurve_apply a t).symm


end NLS.MKdV
