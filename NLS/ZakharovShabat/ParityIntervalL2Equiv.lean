import NLS.ZakharovShabat.ParityIntervalL2Extension
import NLS.ZakharovShabat.PhysicalBaseParity

/-! # Exact isometric restriction from each parity space to the original unit interval -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set
namespace NLS.ZakharovShabat

/-- Actual physical restriction, on one original coefficient parity space. -/
def sourceParityUnitRestriction (r : ℤ) :
    sourceParitySubspace (p := 2) r →L[ℂ] IntervalPairL2 :=
  physicalRestrictionL2CLM.comp ((CoeffPair.toMax 2).toContinuousLinearMap.comp
    (sourceParitySubspace (p := 2) r).subtypeL)

theorem sourceParityUnitRestriction_representative (r : ℤ)
    (a : sourceParitySubspace (p := 2) r) :
    intervalL2Representative (sourceParityUnitRestriction r a) =ᵐ[volume.restrict (Ioc 0 1)]
      physicalBase (CoeffPair.toMax 2 a.val) :=
  physicalRestrictionL2_representative _

/-- A parity Fourier vector is determined by its actual unit-interval L² restriction. -/
theorem sourceParityUnitRestriction_injective (r : ℤ) :
    Function.Injective (sourceParityUnitRestriction r) := by
  have hz : intervalL2Representative (0 : IntervalPairL2) =ᵐ[volume.restrict (Ioc 0 1)]
      (0 : ℝ → ℂ × ℂ) := by
    have hr := sourceParityUnitRestriction_representative r 0
    simp only [map_zero,ZeroMemClass.coe_zero] at hr
    exact hr.trans (ae_restrict_of_ae_restrict_of_subset
      (Ioc_subset_Ioc_right (by norm_num : (1 : ℝ) ≤ 2)) physicalBase_zero)
  have hk (a : sourceParitySubspace (p := 2) r) (ha : sourceParityUnitRestriction r a = 0) : a = 0 := by
    have hr := sourceParityUnitRestriction_representative r a
    rw [ha] at hr
    have he := pairParity_eq_zero_of_physicalBase_unit (CoeffPair.toMax 2 a.val) r a.property (hr.symm.trans hz)
    apply Subtype.ext
    apply (CoeffPair.toMax 2).injective
    simpa only [map_zero,ZeroMemClass.coe_zero] using he
  intro a b h
  apply sub_eq_zero.mp
  apply hk
  rw [map_sub,h,sub_self]

/-- Every original unit-interval L² class has a signed Fourier extension into either parity. -/
theorem sourceParityUnitRestriction_surjective (r : ℤ) :
    Function.Surjective (sourceParityUnitRestriction r) := by
  intro u
  refine ⟨⟨sourceParityIntervalCoefficients r (intervalL2Representative u) (memLp_intervalL2Representative u),
    sourceParityIntervalCoefficients_mem r _ _⟩,?_⟩
  change physicalRestrictionL2 (CoeffPair.toMax 2 (sourceParityIntervalCoefficients r (intervalL2Representative u) (memLp_intervalL2Representative u))) = u
  rw [physicalRestriction_sourceParityIntervalCoefficients,intervalL2OfFunction_representative]

/-- Restriction preserves exactly the original component-sum norm on each parity. -/
theorem norm_sourceParityUnitRestriction (r : ℤ) (a : sourceParitySubspace (p := 2) r) :
    ‖sourceParityUnitRestriction r a‖ = ‖a‖ := by
  let u := sourceParityUnitRestriction r a
  let b : sourceParitySubspace (p := 2) r :=
    ⟨sourceParityIntervalCoefficients r (intervalL2Representative u) (memLp_intervalL2Representative u),
      sourceParityIntervalCoefficients_mem r _ _⟩
  have hb : sourceParityUnitRestriction r b = sourceParityUnitRestriction r a := by
    change physicalRestrictionL2 (CoeffPair.toMax 2 (sourceParityIntervalCoefficients r (intervalL2Representative u) (memLp_intervalL2Representative u))) = u
    rw [physicalRestriction_sourceParityIntervalCoefficients,intervalL2OfFunction_representative]
  have he := sourceParityUnitRestriction_injective r hb
  have hn : ‖b‖ = ‖u‖ := by
    change ‖sourceParityIntervalCoefficients r (intervalL2Representative u) (memLp_intervalL2Representative u)‖ = ‖u‖
    rw [norm_sourceParityIntervalCoefficients,intervalL2OfFunction_representative]
  rw [he] at hn
  exact hn.symm

def sourceParityUnitIsometry (r : ℤ) : sourceParitySubspace (p := 2) r →ₗᵢ[ℂ] IntervalPairL2 where
  toLinearMap := (sourceParityUnitRestriction r).toLinearMap
  norm_map' := norm_sourceParityUnitRestriction r

/-- Either full parity Hilbert space is exactly the physical unit-interval L² space. -/
def sourceParityUnitEquiv (r : ℤ) : sourceParitySubspace (p := 2) r ≃ₗᵢ[ℂ] IntervalPairL2 :=
  LinearIsometryEquiv.ofSurjective (sourceParityUnitIsometry r) (sourceParityUnitRestriction_surjective r)

@[simp] theorem sourceParityUnitEquiv_apply (r : ℤ) (a : sourceParitySubspace (p := 2) r) :
    sourceParityUnitEquiv r a = sourceParityUnitRestriction r a := rfl

/-- The isometry is actual restriction of the physical Fourier representative. -/
theorem sourceParityUnitEquiv_representative (r : ℤ) (a : sourceParitySubspace (p := 2) r) :
    intervalL2Representative (sourceParityUnitEquiv r a) =ᵐ[volume.restrict (Ioc 0 1)]
      physicalBase (CoeffPair.toMax 2 a.val) := sourceParityUnitRestriction_representative r a

end NLS.ZakharovShabat
