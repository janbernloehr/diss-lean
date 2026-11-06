import NLS.KdV.HillSmoothHierarchyTraceLimit
import NLS.KdV.HillHighMomentSigns
import NLS.KdV.HillContinuousReality
import NLS.ComplexAnalysis.NonnegativeComplexSeries
import Mathlib.Topology.Algebra.InfiniteSum.Module

/-! # The complete actual smooth physical hierarchy moment trace, including its nonlinear convolution. -/

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ContDiff ComplexConjugate
namespace NLS.KdV
open NLS.ComplexAnalysis
theorem hasSum_hillL2Moments_hierarchy_smooth
    (Q : C(AddCircle (2 : ℝ), ℂ))
    (hq : SpectralWeight.one.toCoeff (hillContinuousCoefficients Q) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))
    (hreal : ∀ x : AddCircle (2 : ℝ), (Q x).im = 0)
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2 : ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) 1)
    (hmean : (∫ x in (0 : ℝ)..1, Q (x : AddCircle (2 : ℝ))) = 0) (m : ℕ) :
    HasSum (fun k : ℕ => (2*(k+1 : ℕ)*Real.pi : ℂ) *
      hillL2RealContourMoment (hillContinuousCoefficients Q) hq hr (k+1) m)
      (hillClassicalHierarchyTraceValue (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) m) := by
  let q := hillContinuousCoefficients Q
  let f : ℕ → ℂ := fun n => (2*(n : ℂ)*Real.pi) * hillL2RealContourMoment q hq hr n m
  have hpos : ∀ᶠ k : ℕ in atTop, ∀ m : ℕ, 0 ≤ hillRealGapIntegral q hq hr (k+1) m :=
    (tendsto_add_atTop_nat 1).eventually (eventually_hillRealGapIntegral_nonneg q hq hr)
  have hnonneg : ∀ᶠ k : ℕ in atTop, f (k+1) = (‖f (k+1)‖ : ℂ) := by
    filter_upwards [hpos] with k hk
    have hI := hk m
    dsimp only [f]
    rw [hillL2RealContourMoment_eq_gapIntegral q hq hr (k+1) (by omega)]
    have he : (2*((k+1 : ℕ) : ℂ)*Real.pi) * (hillRealGapIntegral q hq hr (k+1) m : ℂ) =
        ((2*(k+1 : ℕ)*Real.pi*hillRealGapIntegral q hq hr (k+1) m : ℝ) : ℂ) := by push_cast; ring
    rw [he, norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hpartial := tendsto_partial_hillL2Moments_hierarchy_smooth Q hq hr hreal hf hp hmean m
  have he (N : ℕ) : (∑ n ∈ Finset.Icc 1 N, f n) = ∑ k ∈ Finset.range N, f (k+1) := by
    rw [← Finset.Ico_succ_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    simp only [Order.succ_eq_add_one, Nat.add_sub_cancel, Nat.add_comm 1]
  have hlim : Tendsto (fun N => ∑ k ∈ Finset.range N, f (k+1)) atTop
      (𝓝 (hillClassicalHierarchyTraceValue (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) m)) := by
    simpa only [← he] using hpartial
  exact hasSum_of_eventually_nonnegative_real_partial_limit (fun k => f (k+1)) _ hnonneg hlim

theorem hasSum_hillPhysicalMoments_hierarchy_smooth
    (Q : C(AddCircle (2 : ℝ), ℂ))
    (hreal : ∀ x : AddCircle (2 : ℝ), (Q x).im = 0)
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2 : ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) 1)
    (hmean : (∫ x in (0 : ℝ)..1, Q (x : AddCircle (2 : ℝ))) = 0) (m : ℕ) :
    HasSum (fun k : ℕ => (2*(k+1 : ℕ)*Real.pi : ℂ) *
      hillL2RealContourMoment (hillContinuousCoefficients Q) (hillContinuousCoefficients_mem_even Q hp)
        (isRealHillPotential_hillContinuousCoefficients Q hreal) (k+1) m)
      (hillClassicalHierarchyTraceValue (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) m) :=
  hasSum_hillL2Moments_hierarchy_smooth Q (hillContinuousCoefficients_mem_even Q hp)
    (isRealHillPotential_hillContinuousCoefficients Q hreal) hreal hf hp hmean m

theorem hasSum_hillRealMoments_hierarchy_smooth
    (Q : C(AddCircle (2 : ℝ), ℂ))
    (hreal : ∀ x : AddCircle (2 : ℝ), (Q x).im = 0)
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2 : ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) 1)
    (hmean : (∫ x in (0 : ℝ)..1, Q (x : AddCircle (2 : ℝ))) = 0) (m : ℕ) :
    HasSum (fun k : ℕ => (2*(k+1 : ℕ)*Real.pi : ℝ) *
      hillRealGapIntegral (hillContinuousCoefficients Q) (hillContinuousCoefficients_mem_even Q hp)
        (isRealHillPotential_hillContinuousCoefficients Q hreal) (k+1) m)
      ((hillClassicalHierarchyTraceValue (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) m).re) := by
  have h := Complex.reCLM.hasSum (hasSum_hillPhysicalMoments_hierarchy_smooth Q hreal hf hp hmean m)
  have he : (fun k : ℕ => Complex.reCLM ((2*(k+1 : ℕ)*Real.pi : ℂ) *
      hillL2RealContourMoment (hillContinuousCoefficients Q) (hillContinuousCoefficients_mem_even Q hp)
        (isRealHillPotential_hillContinuousCoefficients Q hreal) (k+1) m)) =
      (fun k : ℕ => (2*(k+1 : ℕ)*Real.pi : ℝ) *
        hillRealGapIntegral (hillContinuousCoefficients Q) (hillContinuousCoefficients_mem_even Q hp)
          (isRealHillPotential_hillContinuousCoefficients Q hreal) (k+1) m) := by
    funext k
    rw [hillL2RealContourMoment_eq_gapIntegral _ _ _ (k+1) (by omega)]
    simp
  rw [he] at h
  simpa only [Complex.reCLM_apply, Complex.div_ofNat_re] using h


end NLS.KdV
