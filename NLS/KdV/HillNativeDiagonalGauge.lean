import NLS.KdV.HillNativeComplexCoordinates
import NLS.KdV.HillOffIndexBoundedSequence
import NLS.SequenceSpaces.Reflection
import NLS.SequenceSpaces.CompactGaugeDerivative

/-! The actual signed off-index exponent is analytic into bounded
sequences. Removing it from the native map gives precisely the original
action amplitude times the intrinsic diagonal Cartesian coordinates. -/
noncomputable section
open Set Complex NLS.LpSequence
open scoped ENNReal
namespace NLS.KdV

def hillHminusSignedOffIndexExponent (q : PeriodOneHminusOne) : Coeff ⊤ :=
  (-I) • hillHminusOffIndexAbelianBoundedSequence q +
    I • Coeff.reflection (hillHminusOffIndexAbelianBoundedSequence q)

theorem analyticOnNhd_hillHminusSignedOffIndexExponent :
    AnalyticOnNhd ℂ hillHminusSignedOffIndexExponent hillHminusOffIndexBoundedDomain := by
  intro q hq
  have hb := analyticOnNhd_hillHminusOffIndexAbelianBoundedSequence q hq
  exact (hb.const_smul (c := (-I))).add
    ((((Coeff.reflection (p := ⊤)).toContinuousLinearEquiv.toContinuousLinearMap.analyticAt _).comp hb).const_smul (c := I))

theorem hillHminusOffIndexAbelianBoundedSequence_nonpositive (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusOffIndexBoundedDomain) (k : ℤ) (hk : k ≤ 0) :
    hillHminusOffIndexAbelianBoundedSequence q k = 0 := by
  rw [hillHminusOffIndexAbelianBoundedSequence_apply q hq]
  apply positiveScalarExtension_zero_of_not_mem_range
  rintro ⟨n,hn⟩
  have hp : (0:ℤ) < ((n:ℕ):ℤ) := by exact_mod_cast n.pos
  change ((n:ℕ):ℤ) = k at hn
  omega

theorem hillHminusSignedOffIndexExponent_positive (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusOffIndexBoundedDomain) (n : ℕ+) :
    hillHminusSignedOffIndexExponent q ((n:ℕ):ℤ) = -I*hillHminusOffIndexAbelianCorrection n q := by
  have hn : -((n:ℕ):ℤ) ≤ 0 := by have := n.pos; omega
  simp only [hillHminusSignedOffIndexExponent,lp.coeFn_add,Pi.add_apply,lp.coeFn_smul,
    Pi.smul_apply,smul_eq_mul,Coeff.reflection_apply,
    hillHminusOffIndexAbelianBoundedSequence_nonpositive q hq _ hn,mul_zero,add_zero]
  rw [hillHminusOffIndexAbelianBoundedSequence_apply q hq,positiveScalarExtension_apply]

theorem hillHminusSignedOffIndexExponent_negative (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusOffIndexBoundedDomain) (n : ℕ+) :
    hillHminusSignedOffIndexExponent q (-((n:ℕ):ℤ)) = I*hillHminusOffIndexAbelianCorrection n q := by
  have hn : -((n:ℕ):ℤ) ≤ 0 := by have := n.pos; omega
  simp only [hillHminusSignedOffIndexExponent,lp.coeFn_add,Pi.add_apply,lp.coeFn_smul,
    Pi.smul_apply,smul_eq_mul,Coeff.reflection_apply,neg_neg,
    hillHminusOffIndexAbelianBoundedSequence_nonpositive q hq _ hn,mul_zero,zero_add]
  rw [hillHminusOffIndexAbelianBoundedSequence_apply q hq,positiveScalarExtension_apply]

theorem hillHminusActionAngleNativeDomain_subset_offIndexBounded :
    hillHminusActionAngleNativeDomain ⊆ hillHminusOffIndexBoundedDomain :=
  fun _ h => hillHminusActionAmplitudeDomain_subset_bounded
    (hillHminusActionAngleEnergyDomain_subset (hillHminusActionAngleNativeDomain_subset h)).1

def hillHminusNativeDiagonalMap : PeriodOneHminusOne → WeightedCoeff (Weight.signedSobolev (-1/2)) 2 :=
  WeightedCoeff.removeExponentialSymbol (Weight.signedSobolev (-1/2))
    hillHminusSignedOffIndexExponent hillHminusNativeComplexMap

theorem analyticOnNhd_hillHminusNativeDiagonalMap :
    AnalyticOnNhd ℂ hillHminusNativeDiagonalMap hillHminusActionAngleNativeDomain := by
  intro q hq
  exact WeightedCoeff.analyticAt_removeExponentialSymbol _ _ _ q
    (analyticOnNhd_hillHminusSignedOffIndexExponent q
      (hillHminusActionAngleNativeDomain_subset_offIndexBounded hq))
    (analyticOnNhd_hillHminusNativeComplexMap q hq)

theorem hillHminusNativeDiagonalMap_positive (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusActionAngleNativeDomain) (n : ℕ+) :
    (hillHminusNativeDiagonalMap q).val ((n:ℕ):ℤ) =
      hillHminusCanonicalActionAmplitude n q*hillHminusDiagonalCartesianMinus n q/(Real.sqrt 2:ℂ) := by
  change ((WeightedCoeff.exponentialSymbolEquiv _ (hillHminusSignedOffIndexExponent q)).symm
    (hillHminusNativeComplexMap q)).val _ = _
  rw [WeightedCoeff.exponentialSymbolEquiv_symm_apply,
    hillHminusSignedOffIndexExponent_positive q (hillHminusActionAngleNativeDomain_subset_offIndexBounded hq),
    hillHminusNativeComplexMap_positive q hq]
  unfold hillHminusActionAngleFactorMinus hillHminusAbelianCartesianMinus
  rw [show -(-I*hillHminusOffIndexAbelianCorrection n q) = I*hillHminusOffIndexAbelianCorrection n q by ring]
  have he : Complex.exp (I*hillHminusOffIndexAbelianCorrection n q)*
      Complex.exp (-I*hillHminusOffIndexAbelianCorrection n q) = 1 := by
    rw [← Complex.exp_add,show I*hillHminusOffIndexAbelianCorrection n q+-I*hillHminusOffIndexAbelianCorrection n q=0 by ring,Complex.exp_zero]
  calc
    _ = (hillHminusCanonicalActionAmplitude n q*hillHminusDiagonalCartesianMinus n q)*
      (Complex.exp (I*hillHminusOffIndexAbelianCorrection n q)*Complex.exp (-I*hillHminusOffIndexAbelianCorrection n q))/(Real.sqrt 2:ℂ) := by ring
    _ = _ := by rw [he,mul_one]

theorem hillHminusNativeDiagonalMap_negative (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusActionAngleNativeDomain) (n : ℕ+) :
    (hillHminusNativeDiagonalMap q).val (-((n:ℕ):ℤ)) =
      hillHminusCanonicalActionAmplitude n q*hillHminusDiagonalCartesianPlus n q/(Real.sqrt 2:ℂ) := by
  change ((WeightedCoeff.exponentialSymbolEquiv _ (hillHminusSignedOffIndexExponent q)).symm
    (hillHminusNativeComplexMap q)).val _ = _
  rw [WeightedCoeff.exponentialSymbolEquiv_symm_apply,
    hillHminusSignedOffIndexExponent_negative q (hillHminusActionAngleNativeDomain_subset_offIndexBounded hq),
    hillHminusNativeComplexMap_negative q hq]
  unfold hillHminusActionAngleFactorPlus hillHminusAbelianCartesianPlus
  have he : Complex.exp (-(I*hillHminusOffIndexAbelianCorrection n q))*
      Complex.exp (I*hillHminusOffIndexAbelianCorrection n q) = 1 := by
    rw [← Complex.exp_add,neg_add_cancel,Complex.exp_zero]
  calc
    _ = (hillHminusCanonicalActionAmplitude n q*hillHminusDiagonalCartesianPlus n q)*
      (Complex.exp (-(I*hillHminusOffIndexAbelianCorrection n q))*Complex.exp (I*hillHminusOffIndexAbelianCorrection n q))/(Real.sqrt 2:ℂ) := by ring
    _ = _ := by rw [he,mul_one]

theorem hillHminusNativeDiagonalMap_zero_mode (q : PeriodOneHminusOne) :
    (hillHminusNativeDiagonalMap q).val 0 = 0 := by
  change ((WeightedCoeff.exponentialSymbolEquiv _ (hillHminusSignedOffIndexExponent q)).symm
    (hillHminusNativeComplexMap q)).val 0 = _
  rw [WeightedCoeff.exponentialSymbolEquiv_symm_apply,hillHminusNativeComplexMap_zero_mode,mul_zero]

theorem hillHminusNativeComplexMap_from_diagonal (q : PeriodOneHminusOne) :
    hillHminusNativeComplexMap q =
      WeightedCoeff.exponentialSymbolEquiv (Weight.signedSobolev (-1/2))
        (hillHminusSignedOffIndexExponent q) (hillHminusNativeDiagonalMap q) :=
  ((WeightedCoeff.exponentialSymbolEquiv _ _).apply_symm_apply _).symm

end NLS.KdV
