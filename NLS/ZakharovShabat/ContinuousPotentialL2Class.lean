import NLS.ZakharovShabat.PhysicalIntervalL2
import NLS.ZakharovShabat.ClassicalRemainderL2Bound
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-! # Continuous potentials in the physical L2 space

Use the original two-component L2 classes and identify their class norm
with the square-integral budget used in the fundamental-solution estimates.
-/
noncomputable section
open Set MeasureTheory Filter Topology
open NLS.LinearVolterra
namespace NLS.ZakharovShabat

theorem memLp_extend_continuousPotential (φ : Curve (ℂ × ℂ)) :
    MemLp (extend φ) 2 (volume.restrict (Ioc 0 1)) := by
  apply memLp_prod_iff.mpr
  constructor
  · exact (memLp_two_iff_integrable_sq_norm (continuous_extend φ).fst.aestronglyMeasurable).mpr
      (((continuous_extend φ).fst.norm.pow 2).intervalIntegrable 0 1).1
  · exact (memLp_two_iff_integrable_sq_norm (continuous_extend φ).snd.aestronglyMeasurable).mpr
      (((continuous_extend φ).snd.norm.pow 2).intervalIntegrable 0 1).1

/-- The original physical L2 class of a continuous potential. -/
def continuousPotentialL2Class (φ : Curve (ℂ × ℂ)) : IntervalPairL2 :=
  intervalL2OfFunction (extend φ) (memLp_extend_continuousPotential φ)

theorem continuousPotentialL2Class_representative (φ : Curve (ℂ × ℂ)) :
    intervalL2Representative (continuousPotentialL2Class φ) =ᵐ[volume.restrict (Ioc 0 1)] extend φ :=
  intervalL2Representative_ofFunction _ _

/-- The class norm is exactly the Hilbert L2 budget, with no normalization factor. -/
theorem norm_continuousPotentialL2Class (φ : Curve (ℂ × ℂ)) :
    ‖continuousPotentialL2Class φ‖ = classicalPotentialL2Norm φ := by
  rw [← Real.sqrt_sq (norm_nonneg (continuousPotentialL2Class φ))]
  unfold continuousPotentialL2Class
  rw [norm_sq_intervalL2OfFunction]
  unfold classicalPotentialL2Norm
  apply congrArg Real.sqrt
  exact (intervalIntegral.integral_add
    (((continuous_extend φ).fst.norm.pow 2).intervalIntegrable 0 1)
    (((continuous_extend φ).snd.norm.pow 2).intervalIntegrable 0 1)).symm

@[simp] theorem continuousPotentialL2Class_add (φ ψ : Curve (ℂ × ℂ)) :
    continuousPotentialL2Class (φ+ψ) = continuousPotentialL2Class φ+continuousPotentialL2Class ψ := by
  apply intervalL2Representative_injective
  filter_upwards [continuousPotentialL2Class_representative (φ+ψ),
    continuousPotentialL2Class_representative φ,continuousPotentialL2Class_representative ψ,
    intervalL2Representative_add (continuousPotentialL2Class φ) (continuousPotentialL2Class ψ)] with s h hφ hψ hadd
  rw [h,hadd,hφ,hψ]
  rfl

@[simp] theorem continuousPotentialL2Class_smul (c : ℂ) (φ : Curve (ℂ × ℂ)) :
    continuousPotentialL2Class (c • φ) = c • continuousPotentialL2Class φ := by
  apply intervalL2Representative_injective
  filter_upwards [continuousPotentialL2Class_representative (c • φ),
    continuousPotentialL2Class_representative φ,
    intervalL2Representative_smul c (continuousPotentialL2Class φ)] with s h hφ hc
  rw [h,hc,hφ]
  rfl

/-- Algebraic compatibility with the original physical classes. -/
def continuousPotentialL2LinearMap : Curve (ℂ × ℂ) →ₗ[ℂ] IntervalPairL2 where
  toFun := continuousPotentialL2Class
  map_add' := continuousPotentialL2Class_add
  map_smul' := continuousPotentialL2Class_smul

@[simp] theorem continuousPotentialL2Class_sub (φ ψ : Curve (ℂ × ℂ)) :
    continuousPotentialL2Class (φ-ψ) = continuousPotentialL2Class φ-continuousPotentialL2Class ψ :=
  continuousPotentialL2LinearMap.map_sub φ ψ

@[simp] theorem continuousPotentialL2Class_zero : continuousPotentialL2Class 0 = 0 :=
  continuousPotentialL2LinearMap.map_zero

/-- The distance controlling the extension is the physical L2 distance. -/
theorem dist_continuousPotentialL2Class (φ ψ : Curve (ℂ × ℂ)) :
    dist (continuousPotentialL2Class φ) (continuousPotentialL2Class ψ) = classicalPotentialL2Norm (φ-ψ) := by
  rw [dist_eq_norm,← continuousPotentialL2Class_sub,norm_continuousPotentialL2Class]

end NLS.ZakharovShabat
