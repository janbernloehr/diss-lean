import NLS.KdV.HillContinuousReality
import Mathlib.Topology.Algebra.InfiniteSum.Module
import NLS.KdV.HillSmoothQuadraticTraceLimit
import NLS.ComplexAnalysis.NonnegativeComplexSeries

/-! # The physical quadratic Hill action trace for smooth real potentials

The actual action series sums to the independently defined H_0. The proof
uses the actual contour coefficient and exact finite gap decomposition;
no trace formula, finite-gap density or Birkhoff identification is assumed.
-/

noncomputable section
open Set Complex Filter Topology
open scoped ContDiff
namespace NLS.KdV
open NLS.ComplexAnalysis

theorem hasSum_hillL2Actions_quadraticInvariant_smooth
    (Q : C(AddCircle (2 : ℝ), ℂ))
    (hq : SpectralWeight.one.toCoeff (hillContinuousCoefficients Q) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))
    (hreal : ∀ x : AddCircle (2 : ℝ), (Q x).im = 0)
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2 : ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) 1)
    (hmean : (∫ x in (0 : ℝ)..1, Q (x : AddCircle (2 : ℝ))) = 0) :
    HasSum (fun k : ℕ => (2*(k+1 : ℕ)*Real.pi : ℂ) *
      hillL2RealContourMoment (hillContinuousCoefficients Q) hq hr (k+1) 0)
      (classicalQuadraticInvariant (fun x : ℝ => Q (x : AddCircle (2 : ℝ)))) := by
  let q := hillContinuousCoefficients Q
  let f : ℕ → ℂ := fun n => (2*(n : ℂ)*Real.pi) * hillL2RealContourMoment q hq hr n 0
  have hnonneg (k : ℕ) : f (k+1) = (‖f (k+1)‖ : ℂ) := by
    have hI : 0 ≤ hillRealGapIntegral q hq hr (k+1) 0 := by
      simpa only [mul_zero] using hillRealGapIntegral_nonneg_even q hq hr (k+1) (by omega) 0
    dsimp only [f]
    rw [hillL2RealContourMoment_eq_gapIntegral q hq hr (k+1) (by omega)]
    have he : (2*((k+1 : ℕ) : ℂ)*Real.pi) * (hillRealGapIntegral q hq hr (k+1) 0 : ℂ) =
        ((2*(k+1 : ℕ)*Real.pi*hillRealGapIntegral q hq hr (k+1) 0 : ℝ) : ℂ) := by push_cast; ring
    rw [he, norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hpartial := tendsto_partial_hillL2Actions_quadraticInvariant_smooth Q hq hr hreal hf hp hmean
  have he (N : ℕ) : (∑ n ∈ Finset.Icc 1 N, f n) = ∑ k ∈ Finset.range N, f (k+1) := by
    rw [← Finset.Ico_succ_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    simp only [Order.succ_eq_add_one, Nat.add_sub_cancel, Nat.add_comm 1]
  have hlim : Tendsto (fun N => ∑ k ∈ Finset.range N, f (k+1)) atTop
      (𝓝 (classicalQuadraticInvariant (fun x : ℝ => Q (x : AddCircle (2 : ℝ))))) := by
    simpa only [← he] using hpartial
  exact hasSum_of_nonnegative_real_partial_limit (fun k => f (k+1)) _ hnonneg hlim

theorem tsum_hillL2Actions_quadraticInvariant_smooth
    (Q : C(AddCircle (2 : ℝ), ℂ))
    (hq : SpectralWeight.one.toCoeff (hillContinuousCoefficients Q) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))
    (hreal : ∀ x : AddCircle (2 : ℝ), (Q x).im = 0)
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2 : ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) 1)
    (hmean : (∫ x in (0 : ℝ)..1, Q (x : AddCircle (2 : ℝ))) = 0) :
    (∑' k : ℕ, (2*(k+1 : ℕ)*Real.pi : ℂ) *
      hillL2RealContourMoment (hillContinuousCoefficients Q) hq hr (k+1) 0) =
      classicalQuadraticInvariant (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) :=
  (hasSum_hillL2Actions_quadraticInvariant_smooth Q hq hr hreal hf hp hmean).tsum_eq

/-- The smooth physical trace with Fourier parity and reality derived
from period one and the real-valued physical potential. -/
theorem hasSum_hillPhysicalActions_quadraticInvariant_smooth
    (Q : C(AddCircle (2 : ℝ), ℂ))
    (hreal : ∀ x : AddCircle (2 : ℝ), (Q x).im = 0)
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2 : ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) 1)
    (hmean : (∫ x in (0 : ℝ)..1, Q (x : AddCircle (2 : ℝ))) = 0) :
    HasSum (fun k : ℕ => (2*(k+1 : ℕ)*Real.pi : ℂ) *
      hillL2RealContourMoment (hillContinuousCoefficients Q) (hillContinuousCoefficients_mem_even Q hp)
        (isRealHillPotential_hillContinuousCoefficients_of_conjugate_fourier Q hreal) (k+1) 0)
      (classicalQuadraticInvariant (fun x : ℝ => Q (x : AddCircle (2 : ℝ)))) :=
  hasSum_hillL2Actions_quadraticInvariant_smooth Q (hillContinuousCoefficients_mem_even Q hp)
    (isRealHillPotential_hillContinuousCoefficients_of_conjugate_fourier Q hreal) hreal hf hp hmean

/-- The literal nonnegative real gap-action series has the physical H_0 value. -/
theorem hasSum_hillRealActions_quadraticInvariant_smooth
    (Q : C(AddCircle (2 : ℝ), ℂ))
    (hreal : ∀ x : AddCircle (2 : ℝ), (Q x).im = 0)
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2 : ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) 1)
    (hmean : (∫ x in (0 : ℝ)..1, Q (x : AddCircle (2 : ℝ))) = 0) :
    HasSum (fun k : ℕ => (2*(k+1 : ℕ)*Real.pi : ℝ) *
      hillRealGapIntegral (hillContinuousCoefficients Q) (hillContinuousCoefficients_mem_even Q hp)
        (isRealHillPotential_hillContinuousCoefficients_of_conjugate_fourier Q hreal) (k+1) 0)
      (classicalQuadraticInvariant (fun x : ℝ => Q (x : AddCircle (2 : ℝ)))).re := by
  have h := Complex.reCLM.hasSum (hasSum_hillPhysicalActions_quadraticInvariant_smooth Q hreal hf hp hmean)
  have he : (fun k : ℕ => Complex.reCLM ((2*(k+1 : ℕ)*Real.pi : ℂ) *
      hillL2RealContourMoment (hillContinuousCoefficients Q) (hillContinuousCoefficients_mem_even Q hp)
        (isRealHillPotential_hillContinuousCoefficients_of_conjugate_fourier Q hreal) (k+1) 0)) =
      (fun k : ℕ => (2*(k+1 : ℕ)*Real.pi : ℝ) *
        hillRealGapIntegral (hillContinuousCoefficients Q) (hillContinuousCoefficients_mem_even Q hp)
          (isRealHillPotential_hillContinuousCoefficients_of_conjugate_fourier Q hreal) (k+1) 0) := by
    funext k
    rw [hillL2RealContourMoment_eq_gapIntegral _ _ _ (k+1) (by omega)]
    simp
  rw [he] at h
  exact h

/-- Exact physical unit-interval L2 normalization of the smooth action trace. -/
theorem hasSum_hillRealActions_half_integral_norm_sq_smooth
    (Q : C(AddCircle (2 : ℝ), ℂ))
    (hreal : ∀ x : AddCircle (2 : ℝ), (Q x).im = 0)
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2 : ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) 1)
    (hmean : (∫ x in (0 : ℝ)..1, Q (x : AddCircle (2 : ℝ))) = 0) :
    HasSum (fun k : ℕ => (2*(k+1 : ℕ)*Real.pi : ℝ) *
      hillRealGapIntegral (hillContinuousCoefficients Q) (hillContinuousCoefficients_mem_even Q hp)
        (isRealHillPotential_hillContinuousCoefficients_of_conjugate_fourier Q hreal) (k+1) 0)
      ((1/2 : ℝ) * ∫ x in (0 : ℝ)..1, ‖Q (x : AddCircle (2 : ℝ))‖^2) := by
  rw [← classicalQuadraticInvariant_re_eq_half_integral_norm_sq _ (fun x => hreal (x : AddCircle (2 : ℝ)))]
  exact hasSum_hillRealActions_quadraticInvariant_smooth Q hreal hf hp hmean

end NLS.KdV
