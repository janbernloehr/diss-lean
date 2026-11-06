import NLS.KdV.NativeHillPhysicalSource
import NLS.KdV.HillUnitWeightLift

/-! # The actual bounded original physical direction of every native potential

This complex-linear direction map retains all original unit coefficients,
performs literal even insertion, and commutes with the actual rough source.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.KdV

/-- Native unit-period directions as genuine original even Hill directions. -/
def nativeHillPhysicalDirection (m : ℕ) :
    ScalarSobolev m →L[ℂ] WeightedCoeff SpectralWeight.one.toWeight 2 :=
  (hillUnitWeightLift 2).toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((Coeff.periodDouble (p := 2)).toContinuousLinearMap.comp
      (WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m)))

theorem nativeHillPhysicalDirection_toCoeff (m : ℕ) (q : ScalarSobolev m) :
    SpectralWeight.one.toCoeff (nativeHillPhysicalDirection m q) =
      Coeff.periodDouble (WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) q) :=
  toCoeff_hillUnitWeightLift 2 _

theorem nativeHillPhysicalDirection_coefficients (m : ℕ) (q : ScalarSobolev m) (n : ℤ) :
    (nativeHillPhysicalDirection m q).val (2*n) = q.val n := by
  rw [←SpectralWeight.toCoeff_apply,nativeHillPhysicalDirection_toCoeff,Coeff.periodDouble_even,
    WeightedCoeff.sobolevToL2_apply]

theorem nativeHillPhysicalDirection_even (m : ℕ) (q : ScalarSobolev m) :
    SpectralWeight.one.toCoeff (nativeHillPhysicalDirection m q) ∈ Coeff.paritySubspace 0 := by
  rw [nativeHillPhysicalDirection_toCoeff]
  exact Coeff.periodDouble_mem _

/-- The native physical direction is exactly the existing genuine real
physical source whenever its original unit coefficients are real. -/
theorem nativeHillPhysicalDirection_eq_source (m : ℕ) (q : ScalarSobolev m)
    (hq : ∀ n : ℤ, q.val (-n)=conj (q.val n)) :
    nativeHillPhysicalDirection m q = (nativeHillPhysicalSource m q hq).val := by
  apply Subtype.ext
  funext n
  have he := (nativeHillPhysicalDirection_toCoeff m q).trans (nativeHillPhysicalSource_toCoeff m q hq).symm
  simpa only [SpectralWeight.toCoeff_apply] using congrArg (fun a : Coeff 2 => a n) he

/-- The complete diagram commutes on EVERY complex native direction. -/
theorem nativeHillPhysicalDirection_rough (m : ℕ) (q : ScalarSobolev m) :
    hillOriginalHminusSource (nativeHillPhysicalDirection m q) = nativeHillSource m q := by
  apply Subtype.ext
  funext n
  rw [hillOriginalHminusSource_apply,nativeHillPhysicalDirection_coefficients]
  exact (WeightedCoeff.sobolevInclusion_apply _ q n).symm

/-- The direction map is contractive in the original native norm. -/
theorem norm_nativeHillPhysicalDirection_le (m : ℕ) (q : ScalarSobolev m) :
    ‖nativeHillPhysicalDirection m q‖ ≤ ‖q‖ := by
  change ‖hillUnitWeightLift 2 (Coeff.periodDouble (WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) q))‖ ≤ _
  rw [norm_hillUnitWeightLift,Coeff.norm_periodDouble]
  exact WeightedCoeff.norm_sobolevToL2_le _ q

end NLS.KdV
