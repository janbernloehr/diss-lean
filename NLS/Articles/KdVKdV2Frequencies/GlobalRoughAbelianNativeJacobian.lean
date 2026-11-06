import NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianWeakJacobian
import NLS.Articles.KdVKdV2Frequencies.ArbitraryBaseNativeJacobianUnit

/-! # Full native Jacobian units of the SAME global rough forward map -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies
open NLS.KdV
namespace GlobalRoughAbelianForwardData

/-- Every real mean-zero native base at EVERY nonnegative order has an
actual analytic germ of the SAME global map. Its FULL native mean-zero
Jacobian is a unit at EVERY eligible real mean-zero point in that germ. -/
theorem exists_native_meanZero_jacobian_germ (D : GlobalRoughAbelianForwardData)
    (t : ℝ) (ht : 0 ≤ t) (a : DeletedCoeff 2 0)
    (hr : IsRealPeriodOneHminusOne (periodOneSobolevImageInclusion t ht
      (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (t-1)) a))) :
    ∃ V : Set (WeightedCoeff (Weight.sobolev (t-1)) 2), IsOpen V ∧
      WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (t-1)) a ∈ V ∧
      ∃ C : ℝ, ∃ g : WeightedCoeff (Weight.sobolev (t-1)) 2 → WeightedCoeff (Weight.sobolev (t-1/2)) 2,
        0 ≤ C ∧ AnalyticOnNhd ℂ g V ∧
        (∀ p ∈ V, periodOneSobolevImageInclusion t ht p ∈ D.domain ∧ ‖g p‖ ≤ C ∧
          WeightedCoeff.sobolevInclusion (by linarith : (-1/2 : ℝ) ≤ t-1/2) (g p) =
            D.signed (periodOneSobolevImageInclusion t ht p) ∧ (g p).val 0 = 0) ∧
        ∀ b : DeletedCoeff 2 0,
          WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (t-1)) b ∈ V →
          IsRealPeriodOneHminusOne (periodOneSobolevImageInclusion t ht
            (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (t-1)) b)) →
          IsUnit (fderiv ℂ (nativeMeanZeroAbelianMap t g) b) := by
  let L := WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (t-1))
  let J := WeightedCoeff.meanZeroSobolevInclusion (by linarith : (-1 : ℝ) ≤ t-1)
  let q0 : PeriodOneRealHminusOne := ⟨periodOneSobolevImageInclusion t ht (L a),hr⟩
  let E := D.chart q0
  obtain ⟨V,hV,haV,_hJ,C,g,hC,hga,hd⟩ := D.exists_all_native_signed_germ t ht (L a) hr
  refine ⟨V,hV,haV,C,g,hC,hga,?_,?_⟩
  · intro p hp
    exact ⟨(hd p hp).2.1,(hd p hp).2.2.1,(hd p hp).2.2.2.1,(hd p hp).2.2.2.2.1⟩
  · intro b hb hbr
    have hweakreal : IsRealPeriodOneHminusOne
        (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1)) (J b)) := by
      rw [WeightedCoeff.meanZeroSobolevInclusion_lift]
      exact hbr
    have hw := (D.meanZeroForward_analytic _ (D.real_mem_domain _ hweakreal)).differentiableAt
    have hiw := (ContinuousLinearMap.isUnit_iff_bijective.mp (D.isUnit_fderiv_meanZeroForward (J b) hweakreal)).injective
    exact isUnit_fderiv_nativeMeanZero_of_actual_weak_injective_at E.data E.signs t ht
      D.signed V hV g hga (fun p hp => (hd p hp).2.2.2.1)
      b hb (hd (L b) hb).1 hbr (((hd (L b) hb).2.2.2.2.2 hbr).1) hw hiw

end GlobalRoughAbelianForwardData
end NLS.Articles.KdVKdV2Frequencies
