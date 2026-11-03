import NLS.KdV.SingularHillRieszL2
import NLS.Fourier.CircleContinuousLp

/-! The same actual periodic Riesz contour has continuous representatives
and essential-supremum outputs on the entire source periodic L2 space. -/
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

/-- Continuous representative of every original full periodic H1 vector. -/
def singularHillContinuousDomainInclusion :
    FourierLebesgueSpace (2:ℝ) 1 2 →L[ℂ] C(AddCircle (2:ℝ),ℂ) :=
  (sobolevSynthesis (p := 2) (by simp)).comp
    (sobolevCoefficients 1 2).toContinuousLinearEquiv.toContinuousLinearMap

/-- Its L2 class is exactly the original physical domain inclusion. -/
theorem singularHillContinuousDomainInclusion_toLp
    (f : FourierLebesgueSpace (2:ℝ) 1 2) :
    circleContinuousToLp 2 (singularHillContinuousDomainInclusion f) =
      singularHillL2DomainInclusion f := by
  change ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ
    (sobolevSynthesis (by simp) (sobolevCoefficients 1 2 f)) = _
  rw [toLp_sobolevSynthesis]
  change l2Synthesis (ZakharovShabat.scalarInclusion (sobolevCoefficients 1 2 f)) =
    l2Synthesis (h1L2Coefficients f)
  congr 1
  ext n
  rw [ZakharovShabat.scalarInclusion_apply,h1L2Coefficients_apply]
  rfl

/-- The actual full L2 spectral projection with its continuous representative. -/
def singularHillContinuousRieszProjection
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (r : ℝ) :
    CircleL2 →L[ℂ] C(AddCircle (2:ℝ),ℂ) :=
  singularHillContinuousDomainInclusion.comp
    ((singularHillRieszToH1 q c r).comp singularHillL2BaseInclusion)

/-- The continuous projection realizes exactly the actual L2 projection. -/
theorem singularHillContinuousRieszProjection_toLp
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (r : ℝ) (F : CircleL2) :
    circleContinuousToLp 2 (singularHillContinuousRieszProjection q c r F) =
      singularHillL2RieszProjection q c r F :=
  singularHillContinuousDomainInclusion_toLp _

/-- The actual L2 image equals this continuous circle representative almost everywhere. -/
theorem singularHillL2RieszProjection_representative
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (r : ℝ) (F : CircleL2) :
    singularHillL2RieszProjection q c r F =ᵐ[AddCircle.haarAddCircle]
      singularHillContinuousRieszProjection q c r F := by
  rw [← singularHillContinuousRieszProjection_toLp]
  exact circleContinuousToLp_representative 2 _

/-- The actual source-periodic essential-supremum projection on all L2 inputs. -/
def singularHillLinfRieszProjection
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (r : ℝ) :
    CircleL2 →L[ℂ] Lp ℂ ⊤ (AddCircle.haarAddCircle (T := (2:ℝ))) :=
  (circleContinuousToLp ⊤).comp (singularHillContinuousRieszProjection q c r)

/-- The L-infinity and L2 outputs are the same physical function almost everywhere. -/
theorem singularHillLinfRieszProjection_same_ae
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (r : ℝ) (F : CircleL2) :
    singularHillLinfRieszProjection q c r F =ᵐ[AddCircle.haarAddCircle]
      singularHillL2RieszProjection q c r F :=
  (circleContinuousToLp_representative ⊤ _).trans
    (singularHillL2RieszProjection_representative q c r F).symm

/-- The essential-supremum operator norm is bounded by the actual uniform-output norm. -/
theorem norm_singularHillLinfRieszProjection_sub_le
    (q v : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (r : ℝ) :
    ‖singularHillLinfRieszProjection q c r - singularHillLinfRieszProjection v c r‖ ≤
      ‖singularHillContinuousRieszProjection q c r - singularHillContinuousRieszProjection v c r‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro F
  change ‖circleContinuousToLp ⊤ (singularHillContinuousRieszProjection q c r F) -
    circleContinuousToLp ⊤ (singularHillContinuousRieszProjection v c r F)‖ ≤ _
  rw [← map_sub]
  exact (norm_circleContinuousToLp_le ⊤ _).trans
    ((singularHillContinuousRieszProjection q c r - singularHillContinuousRieszProjection v c r).le_opNorm F)

/-- The source L2 operator norm has the same comparison constant one. -/
theorem norm_singularHillL2RieszProjection_sub_le
    (q v : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (r : ℝ) :
    ‖singularHillL2RieszProjection q c r - singularHillL2RieszProjection v c r‖ ≤
      ‖singularHillContinuousRieszProjection q c r - singularHillContinuousRieszProjection v c r‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro F
  change ‖singularHillL2RieszProjection q c r F - singularHillL2RieszProjection v c r F‖ ≤ _
  rw [← singularHillContinuousRieszProjection_toLp q c r,
    ← singularHillContinuousRieszProjection_toLp v c r,← map_sub]
  exact (norm_circleContinuousToLp_le 2 _).trans
    ((singularHillContinuousRieszProjection q c r - singularHillContinuousRieszProjection v c r).le_opNorm F)

end NLS.KdV
