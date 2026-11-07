import NLS.KdV.HillFractionalSpectralCore
import NLS.KdV.HillL2IntrinsicDiagonalOneSmoothing
import NLS.KdV.HillProductEquationFamilyFactory
import NLS.KdV.MiuraHillPsiOriginalEstimates

/-! # Full native complex map on the negative fractional Hilbert scale

Restore the actual on-index phase, action amplitude and entire off-index
phase to the same retained spectral core, in the full strong target norm.
-/
noncomputable section
open Set Complex Filter Topology NLS.WeightedCoeff NLS.ZakharovShabat
namespace NLS.KdV.HillProductEquationPatch

def fractionalNativeMap (P : HillProductEquationPatch) (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (q : WeightedCoeff (Weight.sobolev (-r)) 2) : WeightedCoeff (Weight.signedSobolev (1/2-r)) 2 :=
  let a := sobolevInclusion (show (-1:ℝ) ≤ -r by linarith) q
  boundedSymbolBilinear _ (NormedSpace.exp (hillHminusSignedOffIndexExponent a))
    (boundedSymbolBilinear _ (hillHminusNormalizedAmplitudeSymbol a)
      (boundedSymbolBilinear _ (NormedSpace.exp (P.physicalOnIndexSignedExponent a))
        (P.fractionalSpectralCore r hr hr1 q)))

private theorem analytic_fractionalNativeMap_of_core (P : HillProductEquationPatch)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num) P.parent.family.originalDomain
      P.parent.family.domain P.parent.family.roots)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) (q : WeightedCoeff (Weight.sobolev (-r)) 2)
    (hq : sobolevInclusion (show (-1:ℝ) ≤ -r by linarith) q ∈
      P.physicalDirichletSource ∩ hillHminusActionAngleNativeDomain)
    (hc : AnalyticAt ℂ (P.fractionalSpectralCore r hr hr1) q) :
    AnalyticAt ℂ (P.fractionalNativeMap r hr hr1) q := by
  let T : WeightedCoeff (Weight.sobolev (-r)) 2 →L[ℂ] PeriodOneHminusOne :=
    sobolevInclusion (show (-1:ℝ) ≤ -r by linarith)
  let w := Weight.signedSobolev (1/2-r)
  have hon := (P.analytic_physicalOnIndexSignedExponent H (T q) hq.1).comp (T.analyticAt q)
  have hoff := (analyticOnNhd_hillHminusSignedOffIndexExponent (T q)
    (hillHminusActionAngleNativeDomain_subset_offIndexBounded hq.2)).comp (T.analyticAt q)
  have hamp := (hillHminusNormalizedAmplitudeSymbol_data.2 (T q)
    (hillHminusActionAngleNativeDomain_subset_amplitude hq.2)).comp (T.analyticAt q)
  have hi : AnalyticAt ℂ (fun a : WeightedCoeff (Weight.sobolev (-r)) 2 =>
      boundedSymbolBilinear w (NormedSpace.exp (P.physicalOnIndexSignedExponent (T a)))
        (P.fractionalSpectralCore r hr hr1 a)) q :=
    ((boundedSymbolBilinear w).analyticAt_bilinear _).comp
      (f := fun a => (NormedSpace.exp (P.physicalOnIndexSignedExponent (T a)),P.fractionalSpectralCore r hr hr1 a))
      (((NormedSpace.exp_analytic _).comp hon).prod hc)
  have hd := ((boundedSymbolBilinear w).analyticAt_bilinear _).comp
    (f := fun a : WeightedCoeff (Weight.sobolev (-r)) 2 =>
      (hillHminusNormalizedAmplitudeSymbol (T a),
        boundedSymbolBilinear w (NormedSpace.exp (P.physicalOnIndexSignedExponent (T a)))
          (P.fractionalSpectralCore r hr hr1 a))) (hamp.prod hi)
  exact ((boundedSymbolBilinear w).analyticAt_bilinear _).comp
    (f := fun a : WeightedCoeff (Weight.sobolev (-r)) 2 =>
      (NormedSpace.exp (hillHminusSignedOffIndexExponent (T a)),
        boundedSymbolBilinear w (hillHminusNormalizedAmplitudeSymbol (T a))
          (boundedSymbolBilinear w (NormedSpace.exp (P.physicalOnIndexSignedExponent (T a)))
            (P.fractionalSpectralCore r hr hr1 a))))
    (((NormedSpace.exp_analytic _).comp hoff).prod hd)

private theorem fractionalNativeMap_raw_of_core (P : HillProductEquationPatch)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) (q : WeightedCoeff (Weight.sobolev (-r)) 2)
    (hq : sobolevInclusion (show (-1:ℝ) ≤ -r by linarith) q ∈ hillHminusActionAngleNativeDomain)
    (hc : ∀ k, (P.fractionalSpectralCore r hr hr1 q).val k =
      (P.physicalSpectralCoreMap (sobolevInclusion (show (-1:ℝ) ≤ -r by linarith) q)).val k)
    (k : ℤ) :
    (P.fractionalNativeMap r hr hr1 q).val k =
      (hillHminusNativeComplexMap (sobolevInclusion (show (-1:ℝ) ≤ -r by linarith) q)).val k := by
  let a : PeriodOneHminusOne := sobolevInclusion (show (-1:ℝ) ≤ -r by linarith) q
  rw [fractionalNativeMap]
  simp only [boundedSymbolBilinear_apply,Coeff.infty_exp_apply,hc]
  rw [hillHminusNativeComplexMap_from_diagonal,exponentialSymbolEquiv_apply,
    hillHminusNativeDiagonalMap_from_intrinsic a hq,boundedSymbolBilinear_apply,
    P.intrinsicDiagonalMap_from_physicalCore a,exponentialSymbolEquiv_apply]

theorem exists_retained_fractionalNativeMap_analytic
    (P : HillProductEquationPatch)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num) P.parent.family.originalDomain
      P.parent.family.domain P.parent.family.roots)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) (q : WeightedCoeff (Weight.sobolev (-r)) 2)
    (hq : sobolevInclusion (show (-1:ℝ) ≤ -r by linarith) q ∈ P.source)
    (hqreal : IsRealPeriodOneHminusOne (sobolevInclusion (show (-1:ℝ) ≤ -r by linarith) q)) :
    ∃ U : Set (WeightedCoeff (Weight.sobolev (-r)) 2), IsOpen U ∧ q ∈ U ∧
      AnalyticOnNhd ℂ (P.fractionalNativeMap r hr hr1) U ∧
      ∀ a ∈ U, ∀ k, (P.fractionalNativeMap r hr hr1 a).val k =
        (hillHminusNativeComplexMap (sobolevInclusion (show (-1:ℝ) ≤ -r by linarith) a)).val k := by
  obtain ⟨U,hU,hqU,hUP,hcore,hraw⟩ := P.exists_retained_fractionalSpectralCore_analytic H r hr hr1 q hq hqreal
  exact ⟨U,hU,hqU,fun a ha => P.analytic_fractionalNativeMap_of_core H r hr hr1 a (hUP a ha) (hcore a ha),
    fun a ha k => P.fractionalNativeMap_raw_of_core r hr hr1 a (hUP a ha).2 (hraw a ha) k⟩

end NLS.KdV.HillProductEquationPatch
namespace NLS.KdV

/-- No supplied patch, lift or estimate: the SAME actual full native map
has a strong analytic fractional realization near every real H^(-r) input. -/
theorem exists_hillFractionalNativeMap_analytic
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) (q : WeightedCoeff (Weight.sobolev (-r)) 2)
    (hqreal : IsRealPeriodOneHminusOne (WeightedCoeff.sobolevInclusion (show (-1:ℝ) ≤ -r by linarith) q)) :
    ∃ F : WeightedCoeff (Weight.sobolev (-r)) 2 → WeightedCoeff (Weight.signedSobolev (1/2-r)) 2,
      ∃ U : Set (WeightedCoeff (Weight.sobolev (-r)) 2), IsOpen U ∧ q ∈ U ∧ AnalyticOnNhd ℂ F U ∧
        ∀ a ∈ U, ∀ k, (F a).val k =
          (hillHminusNativeComplexMap (WeightedCoeff.sobolevInclusion (show (-1:ℝ) ≤ -r by linarith) a)).val k := by
  let a := WeightedCoeff.sobolevInclusion (show (-1:ℝ) ≤ -r by linarith) q
  obtain ⟨A,H⟩ := exists_miuraHillPsiFamily_with_original_estimates
  obtain ⟨P,hqP,_,hPA⟩ := exists_hillProductEquationPatch_with_family A a hqreal
  have HP : SourceLemma12_12Data (by norm_num) (by norm_num) P.parent.family.originalDomain
      P.parent.family.domain P.parent.family.roots := by rw [hPA]; exact H
  obtain ⟨U,hU,hqU,ha,hraw⟩ := P.exists_retained_fractionalNativeMap_analytic HP r hr hr1 q hqP hqreal
  exact ⟨P.fractionalNativeMap r hr hr1,U,hU,hqU,ha,hraw⟩

end NLS.KdV
