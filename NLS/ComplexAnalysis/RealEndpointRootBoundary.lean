import NLS.ComplexAnalysis.AnalyticTwoZeroRoot
import NLS.ZakharovShabat.SourceStandardRootGapSideJoint

/-! # Full half-plane limits of the standard root of a real segment

This is the existing joint standard-root boundary theorem in endpoint
coordinates. The upper and lower limits have respectively negative and
positive imaginary sign, including at both endpoints.
-/

noncomputable section
open Set Complex Filter Topology
namespace NLS.ComplexAnalysis

theorem endpointRoot_real_gap_limits (a b x : ℝ) (hab : a < b) (hx : x ∈ Icc a b) :
    Tendsto (endpointRoot (a : ℂ) b) (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ))
      (𝓝 (-I*(Real.sqrt ((x-a)*(b-x)) : ℂ))) ∧
    Tendsto (endpointRoot (a : ℂ) b) (𝓝[{z : ℂ | z.im < 0}] (x : ℂ))
      (𝓝 (I*(Real.sqrt ((x-a)*(b-x)) : ℂ))) := by
  let m : ℝ := (a+b)/2
  let d : ℝ := (b-a)/2
  let t : ℝ := (x-m)/d
  have hd : 0 < d := by dsimp only [d]; linarith
  have hdc : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have ht : -1 ≤ t ∧ t ≤ 1 := by
    dsimp only [t]
    constructor
    · rw [le_div_iff₀ hd]
      dsimp only [m,d]
      linarith [hx.1]
    · rw [div_le_iff₀ hd]
      dsimp only [m,d]
      linarith [hx.2]
  have hcoord : m+d*t = x := by dsimp only [t]; field_simp; ring
  have hpoint : (m : ℂ)+(d : ℂ)*(t : ℂ) = (x : ℂ) := by
    rw [← ofReal_mul,← ofReal_add,hcoord]
  have hmid : ((a : ℂ)+(b : ℂ))/2 = (m : ℂ) := by
    simp only [m,ofReal_div,ofReal_add,ofReal_ofNat]
  have hgap : (2*(d : ℂ))^2 = ((b : ℂ)-(a : ℂ))^2 := by
    dsimp only [d]
    push_cast
    ring
  have hfun : endpointRoot (a : ℂ) b =
      NLS.ZakharovShabat.normalizedStandardRoot (m : ℂ) ((2*(d : ℂ))^2) := by
    funext z
    dsimp only [endpointRoot]
    rw [hmid,← hgap]
  have hsideU : NLS.ZakharovShabat.standardRootGapUpperSide (m : ℂ) d = {z : ℂ | 0 < z.im} := by
    ext z
    change 0 < ((z-(m : ℂ))/(d : ℂ)).im ↔ 0 < z.im
    rw [div_ofReal_im,sub_im,ofReal_im,sub_zero,lt_div_iff₀ hd,zero_mul]
  have hsideL : NLS.ZakharovShabat.standardRootGapLowerSide (m : ℂ) d = {z : ℂ | z.im < 0} := by
    ext z
    change ((z-(m : ℂ))/(d : ℂ)).im < 0 ↔ z.im < 0
    rw [div_ofReal_im,sub_im,ofReal_im,sub_zero,div_lt_iff₀ hd,zero_mul]
  have hnonneg : 0 ≤ 1-t^2 := by nlinarith [ht.1,ht.2]
  have hsq : (d*Real.sqrt (1-t^2))^2 = (x-a)*(b-x) := by
    rw [mul_pow,Real.sq_sqrt hnonneg,← hcoord]
    dsimp only [m,d]
    ring
  have hroot : Real.sqrt ((x-a)*(b-x)) = d*Real.sqrt (1-t^2) := by
    rw [← hsq,Real.sqrt_sq (mul_nonneg hd.le (Real.sqrt_nonneg _))]
  have hu := NLS.ZakharovShabat.normalizedStandardRoot_tendsto_gap_upper_side
    (m : ℂ) d t hdc ht.1 ht.2
  have hl := NLS.ZakharovShabat.normalizedStandardRoot_tendsto_gap_lower_side
    (m : ℂ) d t hdc ht.1 ht.2
  rw [← hfun,hsideU,hpoint] at hu
  rw [← hfun,hsideL,hpoint] at hl
  have hvalU : -(d : ℂ)*I*(Real.sqrt (1-t^2) : ℂ) = -I*(Real.sqrt ((x-a)*(b-x)) : ℂ) := by
    rw [hroot,ofReal_mul]
    ring
  have hvalL : (d : ℂ)*I*(Real.sqrt (1-t^2) : ℂ) = I*(Real.sqrt ((x-a)*(b-x)) : ℂ) := by
    rw [hroot,ofReal_mul]
    ring
  exact ⟨hvalU ▸ hu,hvalL ▸ hl⟩

end NLS.ComplexAnalysis
