import NLS.Articles.KdVKdV2Frequencies.ArbitraryBaseMeanZeroPrincipalEquiv
import NLS.Articles.KdVKdV2Frequencies.ActualNativeJacobianUnit

/-! # Actual native Jacobian invertibility at arbitrary real rough bases -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies
open NLS.KdV

/-- For the ACTUAL native germ, compactness from the actual principal
and weak Jacobian injectivity prove bijectivity of its exact mean-zero
Jacobian. No injectivity is inferred from compactness alone. -/
theorem isUnit_fderiv_nativeMeanZero_of_actual_weak_injective_at
    {q0 : PeriodOneHminusOne} (D : RoughAbelianFourierDataAt q0) (e : ℤ → Bool) (t : ℝ) (ht : 0≤t)
    (Z : PeriodOneHminusOne → WeightedCoeff (Weight.sobolev (-1/2)) 2)
    (V : Set (WeightedCoeff (Weight.sobolev (t-1)) 2)) (hV : IsOpen V)
    (g : WeightedCoeff (Weight.sobolev (t-1)) 2 → WeightedCoeff (Weight.sobolev (t-1/2)) 2)
    (hga : AnalyticOnNhd ℂ g V)
    (hcomm : ∀ p∈V, WeightedCoeff.sobolevInclusion (by linarith : (-1/2 : ℝ)≤t-1/2) (g p)=
      Z (periodOneSobolevImageInclusion t ht p))
    (a : DeletedCoeff 2 0)
    (ha : WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (t-1)) a∈V)
    (hq : periodOneSobolevImageInclusion t ht
      (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (t-1)) a)∈ball q0 D.radius)
    (hr : IsRealPeriodOneHminusOne (periodOneSobolevImageInclusion t ht
      (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (t-1)) a)))
    (hc : IsCompactOperator (fderiv ℂ g
      (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (t-1)) a)-
        packetSignedFourierPrincipalAt D e t ht (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (t-1)) a)))
    (hw : DifferentiableAt ℂ (weakMeanZeroAbelianMap Z)
      (WeightedCoeff.meanZeroSobolevInclusion (by linarith : (-1 : ℝ)≤t-1) a))
    (hiw : Function.Injective (fderiv ℂ (weakMeanZeroAbelianMap Z)
      (WeightedCoeff.meanZeroSobolevInclusion (by linarith : (-1 : ℝ)≤t-1) a))) :
    IsUnit (fderiv ℂ (nativeMeanZeroAbelianMap t g) a) := by
  let L := WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (t-1))
  let P := WeightedCoeff.meanZeroWeightedProjectionCLM (Weight.sobolev (t-1/2))
  let J := WeightedCoeff.meanZeroSobolevInclusion (by linarith : (-1 : ℝ)≤t-1)
  let I := WeightedCoeff.meanZeroSobolevInclusion (by linarith : (-1/2 : ℝ)≤t-1/2)
  have hf : DifferentiableAt ℂ (nativeMeanZeroAbelianMap t g) a :=
    P.differentiableAt.comp a ((hga (L a) ha).differentiableAt.comp a L.differentiableAt)
  have he : (fun x => I (nativeMeanZeroAbelianMap t g x)) =ᶠ[𝓝 a]
      (fun x => weakMeanZeroAbelianMap Z (J x)) := by
    filter_upwards [(hV.preimage L.continuous).mem_nhds ha] with x hx
    change WeightedCoeff.meanZeroSobolevInclusion _ (WeightedCoeff.meanZeroWeightedProjectionCLM _ (g (L x)))=
      WeightedCoeff.meanZeroWeightedProjectionCLM (Weight.sobolev (-1/2))
        (Z (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1)) (WeightedCoeff.meanZeroSobolevInclusion _ x)))
    rw [WeightedCoeff.meanZeroSobolevInclusion_projection,hcomm _ hx,
      WeightedCoeff.meanZeroSobolevInclusion_lift]
    rfl
  have hinj := injective_fderiv_of_commuting_embedding J I (nativeMeanZeroAbelianMap t g)
    (weakMeanZeroAbelianMap Z) a hf hw he (WeightedCoeff.meanZeroSobolevInclusion_injective _) hiw
  have hc' : IsCompactOperator (fderiv ℂ (nativeMeanZeroAbelianMap t g) a-
      packetMeanZeroFourierPrincipalAt D e t ht (L a)) :=
    isCompactOperator_fderiv_clm_pre_post_sub L P g a (hga (L a) ha).differentiableAt _ hc
  obtain ⟨Q,hQ⟩ := exists_packetMeanZeroFourierPrincipalAt_equiv D e t ht (L a) hq hr
  rw [←hQ] at hc'
  exact ContinuousLinearMap.isUnit_iff_bijective.mpr
    (bijective_of_compact_sub_equiv_of_injective _ Q hc' hinj)

end NLS.Articles.KdVKdV2Frequencies
