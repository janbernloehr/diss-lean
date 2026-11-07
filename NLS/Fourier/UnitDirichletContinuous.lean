import NLS.Fourier.UnitDirichletL2

/-! The bounded map from the ENTIRE original zero-trace H1 domain to
its IDENTICAL continuous representative on the closed physical unit interval. -/
noncomputable section
open Set
namespace NLS.Fourier
open NLS.ZakharovShabat
local instance dirichletContinuousH1NormedGroup : NormedAddCommGroup UnitDirichletH1 := unitDirichletSubspace.normedAddCommGroup
local instance dirichletContinuousH1NormedSpace : NormedSpace ℂ UnitDirichletH1 := unitDirichletSubspace.normedSpace

/-- Native zero-trace H1 inclusion in the closed-interval uniform norm. -/
def unitDirichletContinuousInclusion : UnitDirichletH1 →L[ℂ] C(Icc (0:ℝ) 1,ℂ) :=
  (ContinuousMap.compCLM ℂ ℂ
    (⟨fun t : Icc (0:ℝ) 1 => (t.val : AddCircle (2:ℝ)),
      (AddCircle.continuous_mk' (2:ℝ)).comp continuous_subtype_val⟩ :
        C(Icc (0:ℝ) 1,AddCircle (2:ℝ)))).comp
    (periodOneSobolevSynthesis.comp unitDirichletSubspace.subtypeL)

/-- Every point, including both boundary traces, is the original position. -/
theorem unitDirichletContinuousInclusion_apply (g : UnitDirichletH1) (x : Icc (0:ℝ) 1) :
    unitDirichletContinuousInclusion g x = unitDirichletRepresentative g x.val := rfl

end NLS.Fourier
