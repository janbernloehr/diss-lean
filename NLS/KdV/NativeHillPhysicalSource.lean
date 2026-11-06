import NLS.KdV.NativeHamiltonianIsospectral
import NLS.KdV.HillUnitRealSourceUnembed
import NLS.KdV.HillHminusOriginalSourceAdapter

/-! # Exact physical Hill source associated with every original native potential

The unit-period native coefficients embed into the original period-two Hill
source by literal even insertion. Its rough source is the original native
H-minus-one inclusion, at every native order without a smoothness premise.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.KdV

/-- The genuine original physical unit source of a real native potential. -/
def nativeHillUnitRealSource (m : ℕ) (q : ScalarSobolev m)
    (hq : ∀ j : ℤ, q.val (-j)=conj (q.val j)) : RealHillWeightedPotential SpectralWeight.one :=
  hillUnitRealSourceLift (WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) q)
    ((periodOneL2Conjugation_fixed_iff _).mpr (by
      intro j
      simpa only [WeightedCoeff.sobolevToL2_apply] using hq j))

/-- The canonical original period-one real Hill potential, with even period-two coefficients. -/
def nativeHillPhysicalSource (m : ℕ) (q : ScalarSobolev m)
    (hq : ∀ j : ℤ, q.val (-j)=conj (q.val j)) : RealPeriodOneHillPotential :=
  hillRealWeightedEmbedding SpectralWeight.one (nativeHillUnitRealSource m q hq)

theorem nativeHillUnitRealSource_toCoeff (m : ℕ) (q : ScalarSobolev m)
    (hq : ∀ j : ℤ, q.val (-j)=conj (q.val j)) :
    SpectralWeight.one.doubleIndex.toCoeff (nativeHillUnitRealSource m q hq).val =
      WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) q :=
  hillUnitRealSourceLift_toCoeff _ _

theorem nativeHillPhysicalSource_toCoeff (m : ℕ) (q : ScalarSobolev m)
    (hq : ∀ j : ℤ, q.val (-j)=conj (q.val j)) :
    SpectralWeight.one.toCoeff (nativeHillPhysicalSource m q hq).val =
      Coeff.periodDouble (WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) q) := by
  rw [nativeHillPhysicalSource,hillRealWeightedEmbedding_toCoeff,nativeHillUnitRealSource_toCoeff]

/-- Every original unit coefficient is retained with no period or amplitude change. -/
theorem nativeHillPhysicalSource_coefficients (m : ℕ) (q : ScalarSobolev m)
    (hq : ∀ j : ℤ, q.val (-j)=conj (q.val j)) (n : ℤ) :
    SpectralWeight.one.toCoeff (nativeHillPhysicalSource m q hq).val (2*n) = q.val n := by
  rw [nativeHillPhysicalSource_toCoeff,Coeff.periodDouble_even,WeightedCoeff.sobolevToL2_apply]

/-- The native rough inclusion is EXACTLY the physical rough Hill source. -/
theorem nativeHillSource_eq_physical (m : ℕ) (q : ScalarSobolev m)
    (hq : ∀ j : ℤ, q.val (-j)=conj (q.val j)) :
    nativeHillSource m q = (hillPhysicalHminusEmbedding (nativeHillPhysicalSource m q hq)).val := by
  apply Subtype.ext
  funext n
  rw [hillPhysicalHminusEmbedding_apply,nativeHillPhysicalSource_coefficients]
  exact WeightedCoeff.sobolevInclusion_apply _ q n

end NLS.KdV
