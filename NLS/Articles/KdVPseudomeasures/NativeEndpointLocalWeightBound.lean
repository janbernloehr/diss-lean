import NLS.Articles.KdVPseudomeasures.OriginalEndpointNativeCompatibility
import NLS.Articles.KdVPseudomeasures.OriginalCanonicalEndpointWeightBound
import NLS.KdV.HillNativeComplexCoordinates
import NLS.KdV.HillActionAngleOriginalEnergyBound

/-! One complex endpoint neighborhood controls the ACTUAL intrinsic
energy weight uniformly at every positive index. -/
noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

theorem exists_endpoint_local_uniform_native_weight_bound
    (r : ℝ) (hr : AdmissiblePredualOrder r)
    (a : WeightedCoeff (Weight.sobolev (-r)) ⊤)
    (har : IsRealPeriodOneHminusOne (endpointNativeInclusion r hr a)) :
    ∃ U : Set (WeightedCoeff (Weight.sobolev (-r)) ⊤), IsOpen U ∧ a ∈ U ∧
      (∀ q ∈ U, endpointNativeInclusion r hr q ∈ hillHminusActionAngleNativeDomain) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ U, ∀ n : ℕ+,
        Weight.sobolev (-r) (n:ℤ)*hillHminusCanonicalCartesianWeight n (endpointNativeInclusion r hr q) ≤ C := by
  obtain ⟨V,hV,haV,C,hC,hbound⟩ := exists_local_uniform_canonical_endpoint_weight_bound r hr (‖a‖+1)
    (endpointNativeInclusion r hr a) har
  let U := (endpointNativeInclusion r hr) ⁻¹' (V ∩ hillHminusActionAngleNativeDomain) ∩ ball a 1
  refine ⟨U,((hV.inter isOpen_hillHminusActionAngleNativeDomain).preimage
    (endpointNativeInclusion r hr).continuous).inter isOpen_ball,
    ⟨⟨haV,real_mem_hillHminusActionAngleNativeDomain _ har⟩,mem_ball_self (by norm_num)⟩,
    (fun _ h => h.1.2),C,hC,?_⟩
  intro q hq n
  have hnorm : ‖periodOneEndpointOriginal r hr.1 q‖ ≤ ‖a‖+1 := by
    apply (norm_periodOneEndpointOriginal_le r hr.1 q).trans
    have hd : ‖q-a‖ < 1 := by simpa only [mem_ball,dist_eq_norm] using hq.2
    have ht := norm_le_norm_sub_add q a
    linarith
  have h := hbound (periodOneEndpointOriginal r hr.1 q) hnorm
    (periodOneEndpointOriginal_periodic r hr.1 q)
  rw [sourceNativePeriodOneCLM_endpointOriginal] at h
  exact h hq.1.1 n

end NLS.Articles.KdVPseudomeasures
