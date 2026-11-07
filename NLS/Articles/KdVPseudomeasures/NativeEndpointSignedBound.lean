import NLS.Articles.KdVPseudomeasures.NativeEndpointLocalWeightBound
import NLS.KdV.HillSignedEndpointBound

/-! Local uniform bounds for every ACTUAL signed nonlinear coordinate in
the literal article target of order one-half minus r, at exponent infinity. -/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

theorem endpoint_signed_bound_on_intersection
    (r : ℝ) (hr : AdmissiblePredualOrder r)
    (V : Set (WeightedCoeff (Weight.sobolev (-r)) ⊤)) (W : Set PeriodOneHminusOne)
    (CF CW : ℝ) (hCF : 0 ≤ CF) (hCW : 0 ≤ CW)
    (hVD : ∀ q ∈ V, endpointNativeInclusion r hr q ∈ hillHminusActionAngleNativeDomain)
    (hW : ∀ q ∈ V, ∀ n : ℕ+, Weight.sobolev (-r) (n:ℤ)*
      hillHminusCanonicalCartesianWeight n (endpointNativeInclusion r hr q) ≤ CW)
    (hF : ∀ y ∈ W, ∀ n : ℕ+,
      ‖hillHminusActionAngleFactorPlus n y‖ ≤ (CF/Real.sqrt (n:ℕ))*hillHminusCanonicalCartesianWeight n y ∧
      ‖hillHminusActionAngleFactorMinus n y‖ ≤ (CF/Real.sqrt (n:ℕ))*hillHminusCanonicalCartesianWeight n y ∧
      ‖hillHminusActionAngleX n y‖ ≤ (CF/Real.sqrt (n:ℕ))*hillHminusCanonicalCartesianWeight n y ∧
      ‖hillHminusActionAngleY n y‖ ≤ (CF/Real.sqrt (n:ℕ))*hillHminusCanonicalCartesianWeight n y)
    (q : WeightedCoeff (Weight.sobolev (-r)) ⊤)
    (hq : q ∈ V ∩ (endpointNativeInclusion r hr) ⁻¹' W) (k : ℤ) :
    ‖(Weight.signedSobolev (1/2-r) k:ℂ)*
      (hillHminusNativeComplexMap (endpointNativeInclusion r hr q)).val k‖ ≤ (2:ℝ)^r*CF*CW := by
  have hn := hVD q hq.1
  have hw := hW q hq.1
  have hf := hF _ hq.2
  generalize hy : endpointNativeInclusion r hr q=y at hn hw hf ⊢
  exact hillHminusNativeComplexMap_signed_endpoint_bound r hr.1 y hn CF CW hCF hCW
    (fun n => ⟨(hf n).1,(hf n).2.1⟩) hw k

theorem exists_endpoint_local_uniform_signed_bound
    (r : ℝ) (hr : AdmissiblePredualOrder r)
    (a : WeightedCoeff (Weight.sobolev (-r)) ⊤)
    (har : IsRealPeriodOneHminusOne (endpointNativeInclusion r hr a)) :
    ∃ U : Set (WeightedCoeff (Weight.sobolev (-r)) ⊤), IsOpen U ∧ a ∈ U ∧
      (∀ q ∈ U, endpointNativeInclusion r hr q ∈ hillHminusActionAngleNativeDomain) ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ q ∈ U, ∀ k : ℤ,
        ‖(Weight.signedSobolev (1/2-r) k:ℂ)*
          (hillHminusNativeComplexMap (endpointNativeInclusion r hr q)).val k‖ ≤ B := by
  obtain ⟨V,hV,haV,hVD,CW,hCW,hW⟩ := exists_endpoint_local_uniform_native_weight_bound r hr a har
  obtain ⟨W,hWopen,haW,_,CF,hCF,hF⟩ := exists_local_uniform_actionAngle_original_energy_bound
    (endpointNativeInclusion r hr a) har
  let U := V ∩ (endpointNativeInclusion r hr) ⁻¹' W
  let B := (2:ℝ)^r*CF*CW
  have hB : 0 ≤ B := mul_nonneg (mul_nonneg
    (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) r) hCF.le) hCW
  refine ⟨U,hV.inter (hWopen.preimage (endpointNativeInclusion r hr).continuous),⟨haV,haW⟩,
    (fun q hq => hVD q hq.1),B,hB,endpoint_signed_bound_on_intersection r hr V W CF CW hCF.le hCW hVD hW hF⟩

end NLS.Articles.KdVPseudomeasures
