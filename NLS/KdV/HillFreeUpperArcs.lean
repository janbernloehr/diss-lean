import NLS.KdV.HillL2BandAnchors
import NLS.KdV.HillL2CutBounds
import NLS.ZakharovShabat.FreeSineExteriorBounds
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-! # Free half-lattice frequency arcs for actual Hill exterior contours

Squaring a quarter frequency circle gives the upper energy semicircle.
Its whole frequency circle stays uniformly separated from the free
lattice. The actual upper primitive is continuous along the closed arc.
-/

noncomputable section
open Set Metric Complex Filter Topology
open NLS.ZakharovShabat NLS.ComplexAnalysis
namespace NLS.KdV

def hillFreeUpperFrequency (n : ℕ) (t : ℝ) : ℂ := circleMap 0 (hillFreeBandFrequency n) (t/2)

theorem hillFreeBandFrequency_pos (n : ℕ) : 0 < hillFreeBandFrequency n := by
  dsimp [hillFreeBandFrequency]
  positivity

theorem norm_hillFreeUpperFrequency (n : ℕ) (t : ℝ) :
    ‖hillFreeUpperFrequency n t‖ = hillFreeBandFrequency n := by
  rw [hillFreeUpperFrequency, norm_circleMap_zero, abs_of_pos (hillFreeBandFrequency_pos n)]

theorem hillFreeUpperFrequency_zero (n : ℕ) : hillFreeUpperFrequency n 0 = freeCosineZero n := by
  simp only [hillFreeUpperFrequency, zero_div, circleMap_zero, ofReal_zero, zero_mul, exp_zero, mul_one,
    ofReal_hillFreeBandFrequency]

theorem hillFreeUpperFrequency_sq (n : ℕ) (t : ℝ) :
    hillFreeUpperFrequency n t ^ 2 = circleMap 0 ((hillFreeBandFrequency n)^2) t := by
  rw [hillFreeUpperFrequency, circleMap_zero_pow]
  congr 1
  ring

theorem hillFreeUpperFrequency_im_nonneg (n : ℕ) (t : ℝ) (ht : t ∈ Icc 0 Real.pi) :
    0 ≤ (hillFreeUpperFrequency n t).im := by
  rw [hillFreeUpperFrequency, circleMap_zero_im]
  exact mul_nonneg (hillFreeBandFrequency_pos n).le
    (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [ht.1]) (by linarith [ht.2, Real.pi_pos]))

theorem hillFreeUpperFrequency_sq_im_nonneg (n : ℕ) (t : ℝ) (ht : t ∈ Icc 0 Real.pi) :
    0 ≤ (hillFreeUpperFrequency n t ^ 2).im := by
  rw [hillFreeUpperFrequency_sq, circleMap_zero_im]
  exact mul_nonneg (sq_nonneg _) (Real.sin_nonneg_of_nonneg_of_le_pi ht.1 ht.2)

theorem hillFreeBandRadius_separated (n : ℕ) (z : ℂ)
    (hz : ‖z‖ = hillFreeBandFrequency n) (k : ℤ) : Real.pi/4 ≤ ‖z-(Real.pi : ℂ)*k‖ := by
  have hs := freeCosineZero_separated n |k|
  have he : ‖freeCosineZero n-(Real.pi : ℂ)*(|k| : ℤ)‖ =
      abs (hillFreeBandFrequency n - Real.pi*|(k : ℝ)|) := by
    rw [← ofReal_hillFreeBandFrequency, ← ofReal_intCast, ← ofReal_mul, ← ofReal_sub,
      norm_real, Real.norm_eq_abs, Int.cast_abs]
  rw [he] at hs
  have hk : ‖(Real.pi : ℂ)*k‖ = Real.pi*|(k : ℝ)| := by
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, norm_intCast]
  have hnorm := abs_norm_sub_norm_le z ((Real.pi : ℂ)*k)
  rw [hz, hk] at hnorm
  exact hs.trans hnorm

theorem exists_hillFreeUpperFrequency_sinh_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, ∀ t ∈ Icc (0 : ℝ) Real.pi,
      c ≤ Real.exp (-(-I*hillFreeUpperFrequency n t).re) * ‖sinh (-I*hillFreeUpperFrequency n t)‖ := by
  obtain ⟨C, hC, hbound⟩ := exists_bound_exp_im_div_sin_of_separated
    (by positivity : 0 < Real.pi/4)
  refine ⟨1/C, by positivity, ?_⟩
  intro n t ht
  let z := hillFreeUpperFrequency n t
  have him : 0 ≤ z.im := hillFreeUpperFrequency_im_nonneg n t ht
  have hs : sin z ≠ 0 := sin_ne_zero_of_notMem_freeLattice
    (notMem_freeLattice_of_separated (by positivity : 0 < Real.pi/4)
      (hillFreeBandRadius_separated n z (norm_hillFreeUpperFrequency n t)))
  have hb := hbound z (hillFreeBandRadius_separated n z (norm_hillFreeUpperFrequency n t))
  rw [norm_div, norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), abs_of_nonneg him] at hb
  have hmul := (div_le_iff₀ (norm_pos_iff.mpr hs)).mp hb
  have hw := mul_le_mul_of_nonneg_left hmul (Real.exp_nonneg (-z.im))
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at hw
  have hsin : ‖sinh (-I*z)‖ = ‖sin z‖ := by
    rw [neg_mul, sinh_neg, norm_neg, mul_comm I, sinh_mul_I, norm_mul, norm_I, mul_one]
  rw [show (-I*z).re = z.im by simp [mul_re], hsin]
  apply (div_le_iff₀ hC).mpr
  simpa only [one_mul, mul_assoc, mul_left_comm, mul_comm] using hw


theorem tendsto_hillFreeBandFrequency : Tendsto hillFreeBandFrequency atTop atTop := by
  have he (n : ℕ) : ‖freeCosineZero n‖ = hillFreeBandFrequency n := by
    rw [← ofReal_hillFreeBandFrequency, norm_real, Real.norm_eq_abs,
      abs_of_pos (hillFreeBandFrequency_pos n)]
  simpa only [he] using tendsto_norm_freeCosineZero

theorem continuousOn_hillL2RealCutPrimitive_upper
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) :
    ContinuousOn (hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q)) {z : ℂ | 0 ≤ z.im} := by
  exact continuousOn_realBoundaryExtension_upper
    (fun z => hillL2ContinuedPrimitive (z, SpectralWeight.one.toCoeff q))
    (hillL2UpperBoundaryPrimitive (SpectralWeight.one.toCoeff q))
    (fun z hz => (analyticOnNhd_hillL2ContinuedPrimitive_off_real q hq hr z hz.ne').continuousAt)
    (tendsto_hillL2UpperBoundaryPrimitive_all q hq hr)

theorem continuous_hillFreeUpperFrequency (n : ℕ) : Continuous (hillFreeUpperFrequency n) :=
  (continuous_circleMap 0 _).comp (continuous_id.div_const 2)

theorem continuous_hillL2FreeUpperArcPrimitive
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) :
    Continuous (fun t : Icc (0 : ℝ) Real.pi =>
      hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) (hillFreeUpperFrequency n t ^ 2)) := by
  exact (continuousOn_hillL2RealCutPrimitive_upper q hq hr).comp_continuous
    (((continuous_hillFreeUpperFrequency n).comp continuous_subtype_val).pow 2)
    (fun t => hillFreeUpperFrequency_sq_im_nonneg n t t.property)

end NLS.KdV
