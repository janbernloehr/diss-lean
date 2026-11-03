import NLS.KdV.HillActionGapRatioAllBase

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

def hillActionGapPrefactor (n : ℕ) : ℂ :=
  Real.sqrt (2*(hillActionGapRatio q hq hr n).re)

def hillLocalActionGapPrefactor (n : ℕ) (p : Coeff 2) : ℂ :=
  Complex.sqrt (2*hillLocalActionGapRatio q hq hr n p)

theorem analyticAt_hillLocalActionGapPrefactor (n : ℕ) (hn : 1 ≤ n) :
    AnalyticAt ℂ (hillLocalActionGapPrefactor q hq hr n) (SpectralWeight.one.toCoeff q) := by
  have hbase := (hillLocalActionGapRatio_eventually_eq_physical q hq hr n hn).self_of_nhds
  have hpos := (hillActionGapRatio_real_positive q hq hr n hn).1
  have hslit : 2*hillLocalActionGapRatio q hq hr n (SpectralWeight.one.toCoeff q) ∈ Complex.slitPlane := by
    rw [hbase,Complex.mem_slitPlane_iff]
    left
    have he : (2*hillActionGapRatio q hq hr n).re = 2*(hillActionGapRatio q hq hr n).re := by norm_num [mul_re]
    rw [he]
    exact mul_pos (by norm_num : (0 : ℝ) < 2) hpos
  have hA : AnalyticAt ℂ (fun p : Coeff 2 => 2*hillLocalActionGapRatio q hq hr n p) (SpectralWeight.one.toCoeff q) :=
    analyticAt_const.mul (analyticAt_hillLocalActionGapRatio q hq hr n hn)
  exact (Complex.differentiableOn_sqrt.analyticAt (Complex.isOpen_slitPlane.mem_nhds hslit)).comp
    (f := fun p : Coeff 2 => 2*hillLocalActionGapRatio q hq hr n p) hA

theorem hillLocalActionGapPrefactor_eventually_eq_physical (n : ℕ) (hn : 1 ≤ n) :
    ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      hillLocalActionGapPrefactor q hq hr n (SpectralWeight.one.toCoeff p.val) =
        hillActionGapPrefactor p.val p.property.1 p.property.2 n := by
  filter_upwards [hillLocalActionGapRatio_eventually_eq_physical q hq hr n hn] with p hp
  have hR := hillActionGapRatio_real_positive p.val p.property.1 p.property.2 n hn
  have he : hillActionGapRatio p.val p.property.1 p.property.2 n =
      ((hillActionGapRatio p.val p.property.1 p.property.2 n).re : ℂ) := by
    apply Complex.ext <;> simp [hR.2]
  rw [hillLocalActionGapPrefactor,hp,he,← ofReal_ofNat,← ofReal_mul,
    Complex.sqrt_of_nonneg (by exact_mod_cast (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hR.1.le)),ofReal_re]
  rfl

theorem sqrt_twice_hillAction_eq_halfLength_mul_prefactor (n : ℕ) (hn : 1 ≤ n) :
    (Real.sqrt (2*hillRealGapIntegral q hq hr n 0) : ℂ) =
      (hillRealGapHalfLength q hq hr n : ℂ)*hillActionGapPrefactor q hq hr n := by
  have h := congrArg Complex.re (hillRealGapIntegral_eq_halfLength_sq_mul_ratio q hq hr n hn)
  rw [← ofReal_pow] at h
  simp only [ofReal_re,mul_re,ofReal_im,zero_mul,sub_zero] at h
  have hδ := (hillRealGapContour_geometry q hq hr n hn).1
  have hR := (hillActionGapRatio_real_positive q hq hr n hn).1
  rw [h,show 2*((hillRealGapHalfLength q hq hr n)^2*(hillActionGapRatio q hq hr n).re) =
    (hillRealGapHalfLength q hq hr n)^2*(2*(hillActionGapRatio q hq hr n).re) by ring,
    Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq hδ,ofReal_mul]
  rfl

end NLS.KdV
