import NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianNativeJacobian
import NLS.ComplexAnalysis.AnalyticOpenInverse

/-! # Actual analytic inverse charts at every real rough and native base

These are inverse charts of the SAME global forward map, with literal
raw coefficient recovery. Global bijectivity is a separate obligation.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies
open NLS.KdV
namespace GlobalRoughAbelianForwardData

/-- The SAME global map admits an actual two-sided native complex
analytic weak inverse chart at EVERY real mean-zero rough base. -/
theorem exists_weak_analytic_inverse_at (D : GlobalRoughAbelianForwardData)
    (a : DeletedCoeff 2 0)
    (hr : IsRealPeriodOneHminusOne (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1)) a)) :
    ∃ P : OpenPartialHomeomorph (DeletedCoeff 2 0) (DeletedCoeff 2 0),
      (P : DeletedCoeff 2 0 → DeletedCoeff 2 0) = D.meanZeroForward ∧
      a ∈ P.source ∧ P.source ⊆ D.meanZeroDomain ∧
      AnalyticOnNhd ℂ D.meanZeroForward P.source ∧ AnalyticOnNhd ℂ P.symm P.target ∧
      (∀ b ∈ P.source, WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1/2)) (P b) =
        D.signed (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1)) b)) ∧
      ∀ z ∈ P.target, D.signed (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1)) (P.symm z)) =
        WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1/2)) z := by
  have ha : a ∈ D.meanZeroDomain := D.real_mem_domain _ hr
  obtain ⟨P,hP,haP,hsub,hPa,hPia⟩ := NLS.ComplexAnalysis.exists_analytic_openPartialHomeomorph
    D.meanZeroDomain_open D.meanZeroForward_analytic ha (D.isUnit_fderiv_meanZeroForward a hr)
  have hleft (b : DeletedCoeff 2 0) (hb : b ∈ P.source) :
      WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1/2)) (P b) =
        D.signed (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1)) b) := by
    rw [hP]
    exact WeightedCoeff.meanZeroWeightedLift_projection _ _ (D.signed_zero _ (hsub hb))
  refine ⟨P,hP,haP,hsub,hPa,hPia,hleft,?_⟩
  intro z hz
  have hh := hleft (P.symm z) (P.map_target hz)
  rw [P.right_inv hz] at hh
  exact hh.symm

/-- Every real mean-zero base at EVERY native Sobolev order has genuine
OPEN analytic inverse charts of its actual native restriction. Full raw
recovery and exact weak inclusion into the SAME global map are retained. -/
theorem exists_native_analytic_inverse_at (D : GlobalRoughAbelianForwardData)
    (t : ℝ) (ht : 0 ≤ t) (a : DeletedCoeff 2 0)
    (hr : IsRealPeriodOneHminusOne (periodOneSobolevImageInclusion t ht
      (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (t-1)) a))) :
    ∃ V : Set (WeightedCoeff (Weight.sobolev (t-1)) 2), IsOpen V ∧
      WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (t-1)) a ∈ V ∧
      ∃ g : WeightedCoeff (Weight.sobolev (t-1)) 2 → WeightedCoeff (Weight.sobolev (t-1/2)) 2,
        AnalyticOnNhd ℂ g V ∧
        (∀ p ∈ V, periodOneSobolevImageInclusion t ht p ∈ D.domain ∧
          WeightedCoeff.sobolevInclusion (by linarith : (-1/2 : ℝ) ≤ t-1/2) (g p) =
            D.signed (periodOneSobolevImageInclusion t ht p) ∧ (g p).val 0 = 0) ∧
        ∃ P : OpenPartialHomeomorph (DeletedCoeff 2 0) (DeletedCoeff 2 0),
          (P : DeletedCoeff 2 0 → DeletedCoeff 2 0) = nativeMeanZeroAbelianMap t g ∧
          a ∈ P.source ∧ P.source ⊆ (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (t-1))) ⁻¹' V ∧
          AnalyticOnNhd ℂ (nativeMeanZeroAbelianMap t g) P.source ∧ AnalyticOnNhd ℂ P.symm P.target ∧
          (∀ b ∈ P.source, WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (t-1/2)) (P b) =
            g (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (t-1)) b)) ∧
          ∀ z ∈ P.target,
            g (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (t-1)) (P.symm z)) =
              WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (t-1/2)) z ∧
            D.signed (periodOneSobolevImageInclusion t ht
              (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (t-1)) (P.symm z))) =
              WeightedCoeff.sobolevInclusion (by linarith : (-1/2 : ℝ) ≤ t-1/2)
                (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (t-1/2)) z) := by
  obtain ⟨V,hV,haV,_C,g,_hC,hga,hd,hu⟩ := D.exists_native_meanZero_jacobian_germ t ht a hr
  let L := WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (t-1))
  let Q := WeightedCoeff.meanZeroWeightedProjectionCLM (Weight.sobolev (t-1/2))
  have hU : IsOpen (L ⁻¹' V) := hV.preimage L.continuous
  have hf : AnalyticOnNhd ℂ (nativeMeanZeroAbelianMap t g) (L ⁻¹' V) := fun b hb =>
    (Q.analyticAt _).comp ((hga (L b) hb).comp (L.analyticAt b))
  obtain ⟨P,hP,haP,hsub,hPa,hPia⟩ := NLS.ComplexAnalysis.exists_analytic_openPartialHomeomorph
    hU hf haV (hu a haV hr)
  have hleft (b : DeletedCoeff 2 0) (hb : b ∈ P.source) :
      WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (t-1/2)) (P b) = g (L b) := by
    rw [hP]
    exact WeightedCoeff.meanZeroWeightedLift_projection _ _ (hd (L b) (hsub hb)).2.2.2
  refine ⟨V,hV,haV,g,hga,fun p hp => ⟨(hd p hp).1,(hd p hp).2.2⟩,
    P,hP,haP,hsub,hPa,hPia,hleft,?_⟩
  intro z hz
  have hh := hleft (P.symm z) (P.map_target hz)
  rw [P.right_inv hz] at hh
  refine ⟨hh.symm,?_⟩
  rw [←(hd (L (P.symm z)) (hsub (P.map_target hz))).2.2.1,←hh]

end GlobalRoughAbelianForwardData
end NLS.Articles.KdVKdV2Frequencies
