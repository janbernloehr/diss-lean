import NLS.KdV.HillL2BandContinuation

/-! # The actual Hill logarithmic differential on the global real cut

The hyperbolic trace identities fix the root through real bands as
well as off the real axis. Differentiating the trace identity gives
the actual logarithmic derivative everywhere on the open cut domain.
-/

noncomputable section
open Set Metric Complex Filter Topology
namespace NLS.KdV

def hillL2RealCutRoot (q : Coeff 2) (z : ℂ) : ℂ :=
  2 * sinh (hillL2RealCutPrimitive q z)

theorem hillL2RealCutPrimitive_trace
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (z : ℂ) :
    2 * cosh (hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) z) =
      hillL2Discriminant (SpectralWeight.one.toCoeff q) z := by
  by_cases hi : z.im = 0
  · have hzC : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hi]
    simpa only [hillL2RealCutPrimitive, if_pos hi, ← hzC] using
      (hillL2UpperBoundary_trace_all q hq hr z.re).1
  · simpa only [hillL2RealCutPrimitive, if_neg hi] using
      (hillL2ContinuedPrimitive_trace _
        (mem_hillL2ContinuationDomain_of_im_ne_zero q hq hr z hi)).1

theorem hillL2RealCutRoot_eq_source
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (z : ℂ) (hz : z.im ≠ 0) :
    hillL2RealCutRoot (SpectralWeight.one.toCoeff q) z =
      hillL2ContinuedRoot (z, SpectralWeight.one.toCoeff q) := by
  simpa only [hillL2RealCutRoot, hillL2RealCutPrimitive, if_neg hz] using
    (hillL2ContinuedPrimitive_trace _
      (mem_hillL2ContinuationDomain_of_im_ne_zero q hq hr z hz)).2

theorem hillL2RealCutRoot_sq
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (z : ℂ) :
    hillL2RealCutRoot (SpectralWeight.one.toCoeff q) z ^ 2 =
      hillL2Radicand (SpectralWeight.one.toCoeff q) z := by
  dsimp only [hillL2RealCutRoot, hillL2Radicand]
  rw [← hillL2RealCutPrimitive_trace q hq hr z]
  linear_combination -4 * cosh_sq_sub_sinh_sq (hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) z)

theorem hillL2RealCutRoot_ne_zero
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (z : ℂ) (hz : z ∈ hillL2RealCutDomain q hq hr) :
    hillL2RealCutRoot (SpectralWeight.one.toCoeff q) z ≠ 0 := by
  by_cases hi : z.im ≠ 0
  · rw [hillL2RealCutRoot_eq_source q hq hr z hi]
    exact hillL2ContinuedRoot_ne_zero _ (mem_hillL2ContinuationDomain_of_im_ne_zero q hq hr z hi)
  · obtain ⟨n, hn⟩ := hz.resolve_left hi
    have hzC : z = (z.re : ℂ) := by apply Complex.ext <;> simp [not_ne_iff.mp hi]
    have hreg := hillL2Radicand_ne_zero_between_labels q hq hr (2 * n) z.re hn
    intro hzero
    have hs := hillL2RealCutRoot_sq q hq hr z
    rw [hzero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), hzC] at hs
    exact hreg hs.symm

theorem hasDerivAt_hillL2RealCutPrimitive
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (z : ℂ) (hz : z ∈ hillL2RealCutDomain q hq hr) :
    HasDerivAt (hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q))
      (deriv (hillL2Discriminant (SpectralWeight.one.toCoeff q)) z /
        hillL2RealCutRoot (SpectralWeight.one.toCoeff q) z) z := by
  have hF := ((analyticOnNhd_hillL2RealCutPrimitive q hq hr) z hz).differentiableAt.hasDerivAt
  have heq : (fun w => 2 * cosh (hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) w)) =ᶠ[𝓝 z]
      hillL2Discriminant (SpectralWeight.one.toCoeff q) := by
    filter_upwards [(isOpen_hillL2RealCutDomain q hq hr).mem_nhds hz] with w hw
    exact hillL2RealCutPrimitive_trace q hq hr w
  have hd := ((hF.ccosh).const_mul 2).congr_of_eventuallyEq heq.symm
  have he := hd.unique (analyticOnNhd_hillL2Discriminant (SpectralWeight.one.toCoeff q) z
    (mem_univ _)).differentiableAt.hasDerivAt
  have hcoef : deriv (hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q)) z =
      deriv (hillL2Discriminant (SpectralWeight.one.toCoeff q)) z /
        hillL2RealCutRoot (SpectralWeight.one.toCoeff q) z := by
    apply (eq_div_iff (hillL2RealCutRoot_ne_zero q hq hr z hz)).mpr
    change _ * (2 * sinh _) = _
    linear_combination he
  exact hcoef ▸ hF

end NLS.KdV
