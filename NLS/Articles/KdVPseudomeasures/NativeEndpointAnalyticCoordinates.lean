import NLS.Articles.KdVPseudomeasures.NativeEndpointSignedBound

/-! The ACTUAL nonlinear signed map in the endpoint target, with FULL
Banach analyticity near every real source. This is a restriction of the
previously constructed native map, not a separately chosen coordinate map. -/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

def hillEndpointSignedMap (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : WeightedCoeff (Weight.sobolev (-r)) ⊤) :
    WeightedCoeff (Weight.signedSobolev (1/2-r)) ⊤ :=
  WeightedCoeff.ofFunctionOrZero _ ⊤ (hillHminusNativeComplexMap (endpointNativeInclusion r hr q)).val

theorem exists_hillEndpointSignedMap_analytic_neighborhood
    (r : ℝ) (hr : AdmissiblePredualOrder r)
    (a : WeightedCoeff (Weight.sobolev (-r)) ⊤)
    (har : IsRealPeriodOneHminusOne (endpointNativeInclusion r hr a)) :
    ∃ U : Set (WeightedCoeff (Weight.sobolev (-r)) ⊤), IsOpen U ∧ a ∈ U ∧
      (∀ q ∈ U, endpointNativeInclusion r hr q ∈ hillHminusActionAngleNativeDomain) ∧
      AnalyticOnNhd ℂ (hillEndpointSignedMap r hr) U ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ q ∈ U, ‖hillEndpointSignedMap r hr q‖ ≤ B ∧
        ∀ k : ℤ, (hillEndpointSignedMap r hr q).val k=
          (hillHminusNativeComplexMap (endpointNativeInclusion r hr q)).val k := by
  obtain ⟨U,hU,haU,hUD,B,hB,hbound⟩ := exists_endpoint_local_uniform_signed_bound r hr a har
  have han (k : ℤ) : AnalyticOnNhd ℂ (fun q =>
      (hillHminusNativeComplexMap (endpointNativeInclusion r hr q)).val k) U := by
    intro q hq
    exact ((WeightedCoeff.evalCLM (Weight.signedSobolev (-1/2)) 2 k).analyticAt _).comp
      ((analyticOnNhd_hillHminusNativeComplexMap _ (hUD q hq)).comp
        ((endpointNativeInclusion r hr).analyticAt q))
  have hb (q : WeightedCoeff (Weight.sobolev (-r)) ⊤) (hq : q ∈ U) :
      ∃ b : WeightedCoeff (Weight.signedSobolev (1/2-r)) ⊤,
        (∀ k, b.val k=(hillHminusNativeComplexMap (endpointNativeInclusion r hr q)).val k) ∧ ‖b‖ ≤ B := by
    have hm : Memℓp (fun k => (Weight.signedSobolev (1/2-r) k:ℂ)*
        (hillHminusNativeComplexMap (endpointNativeInclusion r hr q)).val k) ⊤ := by
      apply memℓp_infty
      exact ⟨B,by rintro _ ⟨k,rfl⟩; exact hbound q hq k⟩
    let b : WeightedCoeff (Weight.signedSobolev (1/2-r)) ⊤ :=
      ⟨(hillHminusNativeComplexMap (endpointNativeInclusion r hr q)).val,hm⟩
    refine ⟨b,fun _ => rfl,?_⟩
    change ‖WeightedCoeff.weightEquiv _ ⊤ b‖ ≤ B
    apply lp.norm_le_of_forall_le hB
    intro k
    exact hbound q hq k
  obtain ⟨hana,hrealize⟩ := WeightedCoeff.analytic_realization_of_bound
    (Weight.signedSobolev (1/2-r)) (fun q => (hillHminusNativeComplexMap (endpointNativeInclusion r hr q)).val)
      hU han B hb
  exact ⟨U,hU,haU,hUD,hana,B,hB,hrealize⟩

theorem analyticAt_hillEndpointSignedMap_real (r : ℝ) (hr : AdmissiblePredualOrder r)
    (a : WeightedCoeff (Weight.sobolev (-r)) ⊤)
    (har : IsRealPeriodOneHminusOne (endpointNativeInclusion r hr a)) :
    AnalyticAt ℂ (hillEndpointSignedMap r hr) a := by
  obtain ⟨U,_,haU,_,hana,_⟩ := exists_hillEndpointSignedMap_analytic_neighborhood r hr a har
  exact hana a haU

theorem hillEndpointSignedMap_real_coordinate (r : ℝ) (hr : AdmissiblePredualOrder r)
    (a : WeightedCoeff (Weight.sobolev (-r)) ⊤)
    (har : IsRealPeriodOneHminusOne (endpointNativeInclusion r hr a)) (k : ℤ) :
    (hillEndpointSignedMap r hr a).val k=(hillHminusNativeComplexMap (endpointNativeInclusion r hr a)).val k := by
  obtain ⟨U,_,haU,_,_,B,_,hbound⟩ := exists_hillEndpointSignedMap_analytic_neighborhood r hr a har
  exact (hbound a haU).2 k

end NLS.Articles.KdVPseudomeasures
