import NLS.KdV.HillHminusOneJointGapRoots
import NLS.ComplexAnalysis.TwoEndpointRoot

/-! # The intrinsic high Hill primitive on the full gap complement

The actual filled square and intrinsic normalized factor give an analytic
primitive and discriminant root on the disc minus its actual gap segment.
The root squares to the actual radicand, and the primitive derivative has
the original discriminant-over-root formula. Physical sheet matching is
proved separately.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV

def hillHminusOffGapPrimitive (n : ℕ+) (r : ℝ) (K : ℂ × PeriodOneHminusOne → ℂ)
    (q : PeriodOneHminusOne) (l u z : ℂ) : ℂ :=
  I/(2*((Real.pi : ℂ)*(n : ℕ))) * normalizedStandardRoot ((l+u)/2) ((u-l)^2) z *
    hillHminusJointNormalizedGapRoot n r K (z,q)

def hillHminusOffGapRoot (n : ℕ+) (r : ℝ) (K : ℂ × PeriodOneHminusOne → ℂ)
    (q : PeriodOneHminusOne) (l u z : ℂ) : ℂ :=
  2*(-1 : ℂ)^(n : ℕ)*sinh (hillHminusOffGapPrimitive n r K q l u z)

theorem analyticOnNhd_hillHminusOffGapPrimitive
    (n : ℕ+) (r : ℝ) (K : ℂ × PeriodOneHminusOne → ℂ)
    (q : PeriodOneHminusOne) (l u : ℂ) (U : Set ℂ)
    (hS : AnalyticOnNhd ℂ (fun z => hillHminusJointNormalizedGapRoot n r K (z,q)) U) :
    AnalyticOnNhd ℂ (hillHminusOffGapPrimitive n r K q l u) (U \ segment ℝ l u) := by
  intro z hz
  exact (analyticAt_const.mul (analyticOnNhd_standardRoot_off_segment l u z hz.2)).mul (hS z hz.1)

theorem hillHminusOffGapPrimitive_sq
    (n : ℕ+) (r : ℝ) (hr : 0 < r) (K : ℂ × PeriodOneHminusOne → ℂ)
    (q : PeriodOneHminusOne) (l u : ℂ) (hpair : HillHminusHighGapPair q n r l u)
    (z : ℂ) (hz : z ∉ segment ℝ l u)
    (hf : K (z,q) = -hillHminusGapPolynomial n r (z,q)*hillHminusJointNormalizedGapRoot n r K (z,q)^2 /
      (4*((Real.pi : ℂ)*(n : ℕ))^2)) :
    hillHminusOffGapPrimitive n r K q l u z^2 = K (z,q) := by
  rw [hf,hpair.gapPolynomial_eq hr z,hillHminusOffGapPrimitive,mul_pow,mul_pow,
    div_pow,normalizedStandardRoot_sq_off_segment l u z hz,I_sq]
  ring

theorem hillHminusOffGapPrimitive_trace
    (n : ℕ+) (r : ℝ) (hr : 0 < r) (K : ℂ × PeriodOneHminusOne → ℂ)
    (q : PeriodOneHminusOne) (l u : ℂ) (hpair : HillHminusHighGapPair q n r l u)
    (z : ℂ) (hz : z ∉ segment ℝ l u)
    (hf : K (z,q) = -hillHminusGapPolynomial n r (z,q)*hillHminusJointNormalizedGapRoot n r K (z,q)^2 /
      (4*((Real.pi : ℂ)*(n : ℕ))^2))
    (htrace : squaredCosh (K (z,q)) = (-1 : ℂ)^(n : ℕ)*hillHminusDiscriminant q z/2) :
    2*cosh (hillHminusOffGapPrimitive n r K q l u z) =
      (-1 : ℂ)^(n : ℕ)*hillHminusDiscriminant q z := by
  have he := hillHminusOffGapPrimitive_sq n r hr K q l u hpair z hz hf
  rw [← he,squaredCosh_sq] at htrace
  linear_combination 2*htrace

theorem hillHminusOffGapRoot_sq
    (n : ℕ+) (r : ℝ) (K : ℂ × PeriodOneHminusOne → ℂ)
    (q : PeriodOneHminusOne) (l u z : ℂ)
    (htrace : 2*cosh (hillHminusOffGapPrimitive n r K q l u z) =
      (-1 : ℂ)^(n : ℕ)*hillHminusDiscriminant q z) :
    hillHminusOffGapRoot n r K q l u z^2 = hillHminusRadicand q z := by
  have hs : ((-1 : ℂ)^(n : ℕ))^2 = 1 := by rw [pow_two,← mul_pow]; simp
  have he := congrArg (fun w : ℂ => w^2) htrace
  simp only [mul_pow,hs,one_mul] at he
  dsimp only [hillHminusOffGapRoot,hillHminusRadicand]
  rw [mul_pow,mul_pow,hs,mul_one]
  linear_combination he-4*Complex.cosh_sq_sub_sinh_sq (hillHminusOffGapPrimitive n r K q l u z)

end NLS.KdV
