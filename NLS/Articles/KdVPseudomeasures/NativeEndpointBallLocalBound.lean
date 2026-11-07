import NLS.Articles.KdVPseudomeasures.NativeEndpointAnalyticCoordinates

/-! One native Hminus-one neighborhood of any real center controls the
actual endpoint target norm on an ENTIRE prescribed endpoint norm ball.
The native center need not itself have endpoint regularity. -/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

theorem exists_native_neighborhood_endpoint_ball_bound
    (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ)
    (a : PeriodOneHminusOne) (har : IsRealPeriodOneHminusOne a) :
    ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ a ∈ U ∧ U ⊆ hillHminusActionAngleNativeDomain ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ q : WeightedCoeff (Weight.sobolev (-r)) ⊤, ‖q‖ ≤ R →
        endpointNativeInclusion r hr q ∈ U →
        ‖hillEndpointSignedMap r hr q‖ ≤ B ∧ ∀ k,
          (hillEndpointSignedMap r hr q).val k=(hillHminusNativeComplexMap (endpointNativeInclusion r hr q)).val k := by
  obtain ⟨V,hV,haV,CW,hCW,hweight⟩ := exists_local_uniform_canonical_endpoint_weight_bound r hr R a har
  obtain ⟨W,hW,haW,_,CF,hCF,hfactor⟩ := exists_local_uniform_actionAngle_original_energy_bound a har
  let U := (V ∩ W) ∩ hillHminusActionAngleNativeDomain
  have hU : IsOpen U := (hV.inter hW).inter isOpen_hillHminusActionAngleNativeDomain
  let B := (2 : ℝ)^r*CF*CW
  have hB : 0 ≤ B := mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) r) hCF.le) hCW
  refine ⟨U,hU,⟨⟨haV,haW⟩,real_mem_hillHminusActionAngleNativeDomain a har⟩,
    inter_subset_right,B,hB,?_⟩
  intro q hq hqU
  have hnorm : ‖periodOneEndpointOriginal r hr.1 q‖ ≤ R :=
    (norm_periodOneEndpointOriginal_le r hr.1 q).trans hq
  have hw := hweight (periodOneEndpointOriginal r hr.1 q) hnorm
    (periodOneEndpointOriginal_periodic r hr.1 q)
  rw [sourceNativePeriodOneCLM_endpointOriginal] at hw
  have hb (k : ℤ) : ‖(Weight.signedSobolev (1/2-r) k : ℂ)*
      (hillHminusNativeComplexMap (endpointNativeInclusion r hr q)).val k‖ ≤ B :=
    hillHminusNativeComplexMap_signed_endpoint_bound r hr.1 _ hqU.2 CF CW hCF.le hCW
      (fun n => ⟨(hfactor _ hqU.1.2 n).1,(hfactor _ hqU.1.2 n).2.1⟩) (hw hqU.1.1) k
  have hm : Memℓp (fun k => (Weight.signedSobolev (1/2-r) k : ℂ)*
      (hillHminusNativeComplexMap (endpointNativeInclusion r hr q)).val k) ⊤ :=
    memℓp_infty ⟨B,by rintro _ ⟨k,rfl⟩; exact hb k⟩
  let z : WeightedCoeff (Weight.signedSobolev (1/2-r)) ⊤ :=
    ⟨(hillHminusNativeComplexMap (endpointNativeInclusion r hr q)).val,hm⟩
  have he : hillEndpointSignedMap r hr q=z :=
    WeightedCoeff.ofFunctionOrZero_eq_of_coordinates _ _ z (fun _ => rfl)
  refine ⟨?_,fun k => ?_⟩
  · rw [he]
    change ‖WeightedCoeff.weightEquiv _ ⊤ z‖ ≤ B
    exact lp.norm_le_of_forall_le hB hb
  · rw [he]

end NLS.Articles.KdVPseudomeasures
