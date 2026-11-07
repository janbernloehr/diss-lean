import NLS.KdV.HillNormalizedAmplitudeSymbols
import NLS.KdV.HillNativeOffIndexCompact
import NLS.SequenceSpaces.CompactUnitSymbolDerivative

/-! Removing the normalized action amplitude leaves the actual
intrinsic diagonal Cartesian sequence with its fixed original Fourier
normalization. This sequence is analytic in the same signed Hilbert
target, and the removed amplitude changes its derivative compactly. -/
noncomputable section
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.KdV

theorem hillHminusActionAngleNativeDomain_subset_amplitude :
    hillHminusActionAngleNativeDomain ⊆ hillHminusActionAmplitudeDomain :=
  fun _ h => (hillHminusActionAngleEnergyDomain_subset (hillHminusActionAngleNativeDomain_subset h)).1

def hillHminusIntrinsicDiagonalMap (q : PeriodOneHminusOne) :
    WeightedCoeff (Weight.signedSobolev (-1/2)) 2 :=
  WeightedCoeff.boundedSymbolBilinear (Weight.signedSobolev (-1/2))
    (hillHminusInverseAmplitudeSymbol q) (hillHminusNativeDiagonalMap q)

theorem analyticOnNhd_hillHminusIntrinsicDiagonalMap :
    AnalyticOnNhd ℂ hillHminusIntrinsicDiagonalMap hillHminusActionAngleNativeDomain := by
  intro q hq
  exact ((WeightedCoeff.boundedSymbolBilinear _).analyticAt_bilinear _).comp
    ((hillHminusInverseAmplitudeSymbol_data.2 q
      (hillHminusActionAngleNativeDomain_subset_amplitude hq)).prod
        (analyticOnNhd_hillHminusNativeDiagonalMap q hq))

theorem hillHminusNativeDiagonalMap_from_intrinsic (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusActionAngleNativeDomain) :
    hillHminusNativeDiagonalMap q = WeightedCoeff.boundedSymbolBilinear (Weight.signedSobolev (-1/2))
      (hillHminusNormalizedAmplitudeSymbol q) (hillHminusIntrinsicDiagonalMap q) := by
  apply Subtype.ext
  funext k
  change (hillHminusNativeDiagonalMap q).val k = hillHminusNormalizedAmplitudeSymbol q k*
    (hillHminusInverseAmplitudeSymbol q k*(hillHminusNativeDiagonalMap q).val k)
  rw [← mul_assoc,hillHminusAmplitudeSymbols_product q
    (hillHminusActionAngleNativeDomain_subset_amplitude hq),one_mul]

theorem hillHminusIntrinsicDiagonalMap_positive (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusActionAngleNativeDomain) (n : ℕ+) :
    (hillHminusIntrinsicDiagonalMap q).val ((n:ℕ):ℤ) =
      hillHminusDiagonalCartesianMinus n q/
        (((2*Real.sqrt Real.pi*Real.sqrt (n:ℕ):ℝ):ℂ)*(Real.sqrt 2:ℂ)) := by
  change hillHminusInverseAmplitudeSymbol q ((n:ℕ):ℤ)*
    (hillHminusNativeDiagonalMap q).val ((n:ℕ):ℤ) = _
  rw [hillHminusInverseAmplitudeSymbol_data.1 q (hillHminusActionAngleNativeDomain_subset_amplitude hq),
    Coeff.evenUnitExtension_positive,hillHminusNativeDiagonalMap_positive q hq,hillHminusCanonicalActionAmplitude]
  field_simp [hillHminusActionRatioSqrt_ne_zero n q (hillHminusActionAngleNativeDomain_subset_amplitude hq)]

theorem hillHminusIntrinsicDiagonalMap_negative (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusActionAngleNativeDomain) (n : ℕ+) :
    (hillHminusIntrinsicDiagonalMap q).val (-((n:ℕ):ℤ)) =
      hillHminusDiagonalCartesianPlus n q/
        (((2*Real.sqrt Real.pi*Real.sqrt (n:ℕ):ℝ):ℂ)*(Real.sqrt 2:ℂ)) := by
  change hillHminusInverseAmplitudeSymbol q (-((n:ℕ):ℤ))*
    (hillHminusNativeDiagonalMap q).val (-((n:ℕ):ℤ)) = _
  rw [hillHminusInverseAmplitudeSymbol_data.1 q (hillHminusActionAngleNativeDomain_subset_amplitude hq),
    Coeff.evenUnitExtension_negative,hillHminusNativeDiagonalMap_negative q hq,hillHminusCanonicalActionAmplitude]
  field_simp [hillHminusActionRatioSqrt_ne_zero n q (hillHminusActionAngleNativeDomain_subset_amplitude hq)]

theorem hillHminusIntrinsicDiagonalMap_zero_mode (q : PeriodOneHminusOne) :
    (hillHminusIntrinsicDiagonalMap q).val 0=0 := by
  change hillHminusInverseAmplitudeSymbol q 0*(hillHminusNativeDiagonalMap q).val 0=0
  rw [hillHminusNativeDiagonalMap_zero_mode,mul_zero]

theorem isCompactOperator_hillHminusAmplitudeJacobianDifference (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusActionAngleNativeDomain) :
    IsCompactOperator (fderiv ℂ hillHminusNativeDiagonalMap q-fderiv ℂ hillHminusIntrinsicDiagonalMap q) := by
  have he : hillHminusNativeDiagonalMap =ᶠ[𝓝 q]
      (fun a => WeightedCoeff.boundedSymbolBilinear (Weight.signedSobolev (-1/2))
        (hillHminusNormalizedAmplitudeSymbol a) (hillHminusIntrinsicDiagonalMap a)) := by
    filter_upwards [isOpen_hillHminusActionAngleNativeDomain.mem_nhds hq] with a ha
    exact hillHminusNativeDiagonalMap_from_intrinsic a ha
  rw [he.fderiv_eq]
  exact WeightedCoeff.isCompactOperator_fderiv_boundedSymbol_sub _ (by norm_num) _ _ q
    (hillHminusNormalizedAmplitudeSymbol_data.2 q (hillHminusActionAngleNativeDomain_subset_amplitude hq))
    (analyticOnNhd_hillHminusIntrinsicDiagonalMap q hq)
    (hillHminusNormalizedAmplitudeSymbol_unit_tail q (hillHminusActionAngleNativeDomain_subset_amplitude hq))

theorem isCompactOperator_hillHminusIntrinsicJacobianRemainder (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusActionAngleNativeDomain) :
    IsCompactOperator (fderiv ℂ hillHminusNativeComplexMap q-
      (WeightedCoeff.exponentialSymbolEquiv (Weight.signedSobolev (-1/2))
        (hillHminusSignedOffIndexExponent q)).toContinuousLinearMap.comp
          (fderiv ℂ hillHminusIntrinsicDiagonalMap q)) := by
  let M := (WeightedCoeff.exponentialSymbolEquiv (p := 2) (Weight.signedSobolev (-1/2))
    (hillHminusSignedOffIndexExponent q)).toContinuousLinearMap
  have he : fderiv ℂ hillHminusNativeComplexMap q-M.comp (fderiv ℂ hillHminusIntrinsicDiagonalMap q) =
      hillHminusOffIndexJacobianRemainder q+
        M.comp (fderiv ℂ hillHminusNativeDiagonalMap q-fderiv ℂ hillHminusIntrinsicDiagonalMap q) := by
    apply ContinuousLinearMap.ext
    intro h
    simp only [hillHminusOffIndexJacobianRemainder,sub_apply,add_apply,ContinuousLinearMap.comp_apply,map_sub]
    change (fderiv ℂ hillHminusNativeComplexMap q) h-M ((fderiv ℂ hillHminusIntrinsicDiagonalMap q) h) =
      (fderiv ℂ hillHminusNativeComplexMap q) h-M ((fderiv ℂ hillHminusNativeDiagonalMap q) h)+
        (M ((fderiv ℂ hillHminusNativeDiagonalMap q) h)-M ((fderiv ℂ hillHminusIntrinsicDiagonalMap q) h))
    abel
  change IsCompactOperator (fderiv ℂ hillHminusNativeComplexMap q-M.comp
    (fderiv ℂ hillHminusIntrinsicDiagonalMap q))
  rw [he]
  exact (isCompactOperator_hillHminusOffIndexJacobianRemainder q hq).add
    ((isCompactOperator_hillHminusAmplitudeJacobianDifference q hq).clm_comp M)

end NLS.KdV
