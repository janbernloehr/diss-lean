import NLS.KdV.HillL2AllGapSquares
import NLS.ComplexAnalysis.TwoZeroDeflation
/-! # An actual quadratic action bound from a bounded analytic primitive square on an isolating disc. -/

noncomputable section
set_option autoImplicit false
open Set Metric Complex MeasureTheory NLS.ComplexAnalysis
namespace NLS.KdV

theorem hillRealGapIntegral_le_of_square_bound
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1 ≤ n)
    (c : ℂ) (R B : ℝ) (hR : 0 < R) (hB : 0 ≤ B)
    (hK : AnalyticOnNhd ℂ (hillL2RealGapPrimitiveSquare (SpectralWeight.one.toCoeff q) n) (closedBall c R))
    (hl : (hillRealLabels q hq hr (2*n-1) : ℂ) ∈ closedBall c (R/2))
    (hu : (hillRealLabels q hq hr (2*n) : ℂ) ∈ closedBall c (R/2))
    (hbound : ∀ z ∈ sphere c R, ‖hillL2RealGapPrimitiveSquare (SpectralWeight.one.toCoeff q) n z‖ ≤ B^2) :
    hillRealGapIntegral q hq hr n 0 ≤
      (2*B/R)*(hillRealLabels q hq hr (2*n)-hillRealLabels q hq hr (2*n-1))^2 := by
  let l := hillRealLabels q hq hr (2*n-1)
  let u := hillRealLabels q hq hr (2*n)
  let K := hillL2RealGapPrimitiveSquare (SpectralWeight.one.toCoeff q) n
  have hlu : l ≤ u := monotone_hillRealLabels q hq hr (by omega)
  have hγ : 0 ≤ u-l := sub_nonneg.mpr hlu
  have hcoef : 0 ≤ 2*B/R := by positivity
  by_cases hclosed : l = u
  · rw [hillRealGapIntegral_closed q hq hr n 0 hclosed]
    exact mul_nonneg hcoef (sq_nonneg _)
  have hends := hillRealGapProfile_endpoints q hq hr n hn
  have hfa : K l = 0 := by
    dsimp only [K]
    rw [hillL2RealGapPrimitiveSquare_on_gap q hq hr n hn l ⟨le_rfl,hlu⟩,hends.1]
    simp
  have hfb : K u = 0 := by
    dsimp only [K]
    rw [hillL2RealGapPrimitiveSquare_on_gap q hq hr n hn u ⟨hlu,le_rfl⟩,hends.2]
    simp
  have hab : (l : ℂ) = (u : ℂ) → deriv K l = 0 := by
    intro he
    exact False.elim (hclosed (Complex.ofReal_inj.mp he))
  have hQ := norm_twoZeroQuotient_le K l u c R (B^2) hR hK hl hu hfa hfb hab hbound
  have hrect (x : ℝ) (hx : x ∈ Icc l u) : hillRealGapProfile (SpectralWeight.one.toCoeff q) n x ≤ (2*B/R)*(u-l) := by
    have hxc : (x : ℂ) ∈ closedBall c R := by
      have hseg : (x : ℂ) ∈ segment ℝ (l : ℂ) (u : ℂ) := by
        have himg := mem_image_of_mem Complex.ofRealCLM.toLinearMap.toAffineMap
          (show x ∈ segment ℝ l u by simpa only [segment_eq_Icc hlu] using hx)
        simpa only [image_segment] using! himg
      exact closedBall_subset_closedBall (by linarith : R/2 ≤ R)
        ((convex_closedBall c (R/2)).segment_subset hl hu hseg)
    have hxl : ‖(x : ℂ)-l‖ ≤ u-l := by
      rw [← ofReal_sub,norm_real,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hx.1)]
      linarith [hx.2]
    have hxu : ‖(x : ℂ)-u‖ ≤ u-l := by
      rw [← ofReal_sub,norm_real,Real.norm_eq_abs,abs_of_nonpos (sub_nonpos.mpr hx.2)]
      linarith [hx.1]
    have hp : ‖K x‖ = (hillRealGapProfile (SpectralWeight.one.toCoeff q) n x)^2 := by
      dsimp only [K]
      rw [hillL2RealGapPrimitiveSquare_on_gap q hq hr n hn x hx,norm_pow,norm_real,
        Real.norm_eq_abs,abs_of_nonneg (hillRealGapProfile_nonneg q hq hr n hn x hx)]
    have hsq : (hillRealGapProfile (SpectralWeight.one.toCoeff q) n x)^2 ≤ ((2*B/R)*(u-l))^2 := by
      rw [← hp,twoZeroQuotient_factor K l u hfa hfb hab x,norm_mul,norm_mul]
      calc
        _ ≤ ((u-l)*(u-l))*(4*B^2/R^2) :=
          mul_le_mul (mul_le_mul hxl hxu (norm_nonneg _) hγ) (hQ x hxc) (norm_nonneg _) (mul_nonneg hγ hγ)
        _ = _ := by field_simp; ring
    exact (sq_le_sq₀ (hillRealGapProfile_nonneg q hq hr n hn x hx) (mul_nonneg hcoef hγ)).mp hsq
  have hi := intervalIntegral.integral_mono_on (μ := volume) hlu
    ((continuousOn_hillRealGapProfile q hq hr n hn).intervalIntegrable_of_Icc hlu)
    (intervalIntegrable_const (c := (2*B/R)*(u-l))) hrect
  have hpi : 0 ≤ 2/Real.pi ∧ 2/Real.pi ≤ 1 :=
    ⟨by positivity,(div_le_one Real.pi_pos).mpr (by linarith [Real.pi_gt_three])⟩
  unfold hillRealGapIntegral
  simp only [pow_zero,one_mul]
  calc
    _ ≤ (2/Real.pi)*((u-l)*((2*B/R)*(u-l))) := by
      apply mul_le_mul_of_nonneg_left _ hpi.1
      simpa only [intervalIntegral.integral_const,smul_eq_mul] using hi
    _ ≤ (u-l)*((2*B/R)*(u-l)) := mul_le_of_le_one_left (by positivity) hpi.2
    _ = _ := by ring
end NLS.KdV
