import NLS.SequenceSpaces.WeightedAnalyticPhaseTrajectory
import NLS.SequenceSpaces.FourierRealZeroSpatialGenerator
import NLS.SequenceSpaces.FourierRealPhaseFlow

/-! A bounded complex correction gives analytic trajectories in the
actual real mean-zero Fourier Banach space. On the original odd real
frequencies this extension is exactly the full isometric phase flow. -/
noncomputable section
open Complex
open scoped ENNReal
namespace NLS.WeightedCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {K : Type*} [TopologicalSpace K] [CompactSpace K]
local instance (w : Weight) : NormedSpace ℝ (fourierRealZeroSubmodule w p) :=
  fourierRealZeroSubmodule_normedSpace w
local instance (w : Weight) : NormedSpace ℝ C(K,fourierRealZeroSubmodule w p) :=
  @ContinuousMap.normedSpace K (fourierRealZeroSubmodule w p) inferInstance inferInstance
    inferInstance ℝ inferInstance (fourierRealZeroSubmodule_normedSpace w)

private def realInclusion (w : Weight) : fourierRealZeroSubmodule w p →L[ℝ] WeightedCoeff w p :=
  (((zeroModeSubmodule w p).subtypeL).restrictScalars ℝ).comp (fourierRealZeroSubmodule w p).subtypeL

def fourierRealAnalyticPhaseTrajectory (hp : p ≠ ⊤) (w : Weight) (hw : ∀ k, w (-k)=w k)
    (ω : ℤ → ℝ) (θ : C(K,ℝ)) (b : Coeff ⊤) (a : fourierRealZeroSubmodule w p) :
    C(K,fourierRealZeroSubmodule w p) :=
  ((fourierRealZeroFullProjection (p := p) w hw).compLeftContinuous ℝ K)
    (analyticPhaseTrajectory hp w ω θ b a.val.val)

theorem analyticAt_fourierRealAnalyticPhaseTrajectory (hp : p ≠ ⊤) (w : Weight)
    (hw : ∀ k, w (-k)=w k) (ω : ℤ → ℝ) (θ : C(K,ℝ))
    (x : Coeff ⊤ × fourierRealZeroSubmodule w p) :
    AnalyticAt ℝ (fun y : Coeff ⊤ × fourierRealZeroSubmodule w p =>
      fourierRealAnalyticPhaseTrajectory hp w hw ω θ y.1 y.2) x := by
  have hI := @ContinuousLinearMap.analyticAt ℝ inferInstance
    (fourierRealZeroSubmodule w p) inferInstance (fourierRealZeroSubmodule_normedSpace w)
    (WeightedCoeff w p) inferInstance inferInstance (realInclusion (p := p) w) x.2
  have hi : AnalyticAt ℝ (fun y : Coeff ⊤ × fourierRealZeroSubmodule w p =>
      (y.1,realInclusion (p := p) w y.2)) x :=
    analyticAt_fst.prod (hI.comp analyticAt_snd)
  have hP := @ContinuousLinearMap.analyticAt ℝ inferInstance
    C(K,WeightedCoeff w p) inferInstance inferInstance
    C(K,fourierRealZeroSubmodule w p) inferInstance
    (@ContinuousMap.normedSpace K (fourierRealZeroSubmodule w p) inferInstance inferInstance
      inferInstance ℝ inferInstance (fourierRealZeroSubmodule_normedSpace w))
    ((fourierRealZeroFullProjection (p := p) w hw).compLeftContinuous ℝ K)
    (analyticPhaseTrajectory hp w ω θ x.1 x.2.val.val)
  exact hP.comp (f := fun y : Coeff ⊤ × fourierRealZeroSubmodule w p =>
      analyticPhaseTrajectory hp w ω θ y.1 y.2.val.val)
    (((analyticAt_analyticPhaseTrajectory hp w ω θ _).restrictScalars (𝕜 := ℝ)).comp
      (f := fun y : Coeff ⊤ × fourierRealZeroSubmodule w p => (y.1,realInclusion (p := p) w y.2)) hi)

theorem fourierRealAnalyticPhaseTrajectory_apply (hp : p ≠ ⊤) (w : Weight)
    (hw : ∀ k, w (-k)=w k) (ω : ℤ → ℝ) (θ : C(K,ℝ))
    (b : Coeff ⊤) (a : fourierRealZeroSubmodule w p)
    (freq : ℤ → ℝ) (hodd : ∀ k, freq (-k)= -freq k)
    (hb : ∀ k, (ω k:ℂ)+b k=(freq k:ℂ)) (t : K) :
    fourierRealAnalyticPhaseTrajectory hp w hw ω θ b a t =
      fourierRealZeroPhaseFlow w freq hodd (θ t) a := by
  have he : analyticPhaseTrajectory hp w ω θ b a.val.val t =
      (fourierRealZeroPhaseFlow w freq hodd (θ t) a).val.val := by
    apply Subtype.ext
    funext k
    rw [analyticPhaseTrajectory_apply,fourierRealZeroPhaseFlow_apply,hb]
    congr 2
    push_cast
    ring
  change fourierRealZeroFullProjection w hw (analyticPhaseTrajectory hp w ω θ b a.val.val t) = _
  rw [he,fourierRealZeroFullProjection_inclusion]

end NLS.WeightedCoeff
