import NLS.KdV.SingularDirichletRieszKernel
import NLS.Fourier.UnitIntervalContinuousLp

/-! The ACTUAL original Dirichlet contour projection from ordinary L2
into ordinary essential-supremum L-infinity, with its physical representative
and norm comparison to the identical closed-interval continuous output. -/
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue NLS.ZakharovShabat NLS.LinearVolterra

/-- The ordinary physical unit-interval essential-supremum target space. -/
abbrev IntervalLinf := Lp ℂ ⊤ (volume.restrict (Ioc (0:ℝ) 1))

/-- The SAME native contour projection, on ALL ordinary L2 data, with its
ordinary essential-supremum physical output class. -/
def singularDirichletLinfRieszProjection
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (r : ℝ) :
    IntervalL2 →L[ℂ] IntervalLinf :=
  (unitIntervalContinuousToLp ⊤).comp (singularDirichletContinuousRieszProjection q c r)

/-- The actual L-infinity and L2 outputs are the IDENTICAL physical function
a.e. on [0,1], for EVERY ordinary L2 input, with no validity hypothesis. -/
theorem singularDirichletLinfRieszProjection_eq_L2_ae
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (r : ℝ) (F : IntervalL2) :
    singularDirichletLinfRieszProjection q c r F =ᵐ[volume.restrict (Ioc (0:ℝ) 1)]
      singularDirichletL2RieszProjection q c r F :=
  (unitIntervalContinuousToLp_representative ⊤ _).trans
    (singularDirichletContinuousRieszProjection_representative q c r F).symm

/-- Actual L2-to-essential-supremum differences are controlled by the SAME
actual contour operators in the stronger continuous-output uniform norm. -/
theorem norm_singularDirichletLinfRieszProjection_sub_le_uniform
    (q p : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (r : ℝ) :
    ‖singularDirichletLinfRieszProjection q c r-singularDirichletLinfRieszProjection p c r‖ ≤
      ‖singularDirichletContinuousRieszProjection q c r-singularDirichletContinuousRieszProjection p c r‖ := by
  apply ContinuousLinearMap.opNorm_le_bound
    (singularDirichletLinfRieszProjection q c r-singularDirichletLinfRieszProjection p c r)
    (norm_nonneg (singularDirichletContinuousRieszProjection q c r-singularDirichletContinuousRieszProjection p c r))
  intro F
  change ‖unitIntervalContinuousToLp ⊤ (singularDirichletContinuousRieszProjection q c r F)-
    unitIntervalContinuousToLp ⊤ (singularDirichletContinuousRieszProjection p c r F)‖ ≤ _
  rw [← map_sub]
  exact (norm_unitIntervalContinuousToLp_le ⊤ _).trans
    ((singularDirichletContinuousRieszProjection q c r-singularDirichletContinuousRieszProjection p c r).le_opNorm F)

/-- Its ordinary L2 realization is also EXACTLY the same physical contour operator. -/
theorem singularDirichletL2RieszProjection_eq_continuousToLp
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (r : ℝ) (F : IntervalL2) :
    singularDirichletL2RieszProjection q c r F =
      unitIntervalContinuousToLp 2 (singularDirichletContinuousRieszProjection q c r F) :=
  (unitIntervalContinuousToLp_two_dirichlet _).symm

/-- The source's ordinary L2 operator difference is bounded by its actual
L2-to-uniform difference, with the unit-interval constant exactly one. -/
theorem norm_singularDirichletL2RieszProjection_sub_le_uniform
    (q p : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (r : ℝ) :
    ‖singularDirichletL2RieszProjection q c r-singularDirichletL2RieszProjection p c r‖ ≤
      ‖singularDirichletContinuousRieszProjection q c r-singularDirichletContinuousRieszProjection p c r‖ := by
  apply ContinuousLinearMap.opNorm_le_bound
    (singularDirichletL2RieszProjection q c r-singularDirichletL2RieszProjection p c r)
    (norm_nonneg (singularDirichletContinuousRieszProjection q c r-singularDirichletContinuousRieszProjection p c r))
  intro F
  change ‖singularDirichletL2RieszProjection q c r F-singularDirichletL2RieszProjection p c r F‖ ≤ _
  rw [singularDirichletL2RieszProjection_eq_continuousToLp,
    singularDirichletL2RieszProjection_eq_continuousToLp,← map_sub]
  exact (norm_unitIntervalContinuousToLp_le 2 _).trans
    ((singularDirichletContinuousRieszProjection q c r-singularDirichletContinuousRieszProjection p c r).le_opNorm F)

end NLS.KdV
