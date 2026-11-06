import NLS.KdV.HillHminusOnePrimitiveSquareSheets
import NLS.ComplexAnalysis.RealGapSquareRoot

/-! # The actual closed real-gap primitive profile

The intrinsic normalized root gives the principal square root on the
entire actual gap, including both endpoints and a collapsed gap.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV

theorem HillHminusHighGapPair.exists_real_ordered
    {q : PeriodOneHminusOne} {n : ℕ+} {r : ℝ} {l u : ℂ}
    (h : HillHminusHighGapPair q n r l u) (hq : IsRealPeriodOneHminusOne q) :
    ∃ a b : ℝ, a ≤ b ∧ HillHminusHighGapPair q n r (a : ℂ) (b : ℂ) := by
  have hr := h.im_eq_zero hq
  have hl : (l.re : ℂ) = l := by apply Complex.ext <;> simp [hr.1]
  have hu : (u.re : ℂ) = u := by apply Complex.ext <;> simp [hr.2]
  rcases le_total l.re u.re with hle | hle
  · exact ⟨l.re,u.re,hle,by rw [hl,hu]; exact h⟩
  · exact ⟨u.re,l.re,hle,by rw [hu,hl]; exact h.swap⟩

theorem HillHminusHighGapPair.real_gap_mem_ball
    {q : PeriodOneHminusOne} {n : ℕ+} {r : ℝ} {l u : ℝ}
    (h : HillHminusHighGapPair q n r (l : ℂ) (u : ℂ)) (x : ℝ) (hx : x ∈ Icc l u) :
    (x : ℂ) ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) :=
  ofReal_mem_convex_of_mem_Icc _ (convex_ball _ _) l u x h.left_mem h.right_mem hx

theorem hillHminus_real_gap_sqrt_value
    (n : ℕ+) (r epsilon : ℝ) (hr : 0 < r) (hepsilon : epsilon < 1)
    (K : ℂ × PeriodOneHminusOne → ℂ) (q : PeriodOneHminusOne) (l u : ℝ)
    (hpair : HillHminusHighGapPair q n r (l : ℂ) (u : ℂ))
    (hf : ∀ z ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r),
      K (z,q) = -hillHminusGapPolynomial n r (z,q)*hillHminusJointNormalizedGapRoot n r K (z,q)^2 /
        (4*((Real.pi : ℂ)*(n : ℕ))^2))
    (hnorm : ∀ z ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r),
      ‖hillHminusJointNormalizedGapRoot n r K (z,q)-1‖ ≤ epsilon)
    (x : ℝ) (hx : x ∈ Icc l u) :
    Complex.sqrt (K ((x : ℂ),q)) =
      (((Real.sqrt ((x-l)*(u-x))/(2*(Real.pi*(n : ℕ))) : ℝ) : ℂ)) *
        hillHminusJointNormalizedGapRoot n r K ((x : ℂ),q) := by
  have hxball := hpair.real_gap_mem_ball x hx
  have he := hf (x : ℂ) hxball
  rw [hpair.gapPolynomial_eq hr] at he
  apply principalSqrt_real_gap_factor (Real.pi*(n : ℕ)) l u x (by positivity) hx _ _
    ((hnorm _ hxball).trans_lt hepsilon)
  simpa only [ofReal_mul,ofReal_natCast,neg_mul] using he

theorem hillHminus_real_gap_sqrt_continuousAt
    (n : ℕ+) (r epsilon : ℝ) (hr : 0 < r) (hepsilon : epsilon < 1)
    (K : ℂ × PeriodOneHminusOne → ℂ) (q : PeriodOneHminusOne) (l u : ℝ)
    (hpair : HillHminusHighGapPair q n r (l : ℂ) (u : ℂ))
    (hf : ∀ z ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r),
      K (z,q) = -hillHminusGapPolynomial n r (z,q)*hillHminusJointNormalizedGapRoot n r K (z,q)^2 /
        (4*((Real.pi : ℂ)*(n : ℕ))^2))
    (hnorm : ∀ z ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r),
      ‖hillHminusJointNormalizedGapRoot n r K (z,q)-1‖ ≤ epsilon)
    (x : ℝ) (hx : x ∈ Icc l u) :
    ContinuousAt Complex.sqrt (K ((x : ℂ),q)) := by
  have hxball := hpair.real_gap_mem_ball x hx
  have he := hf (x : ℂ) hxball
  rw [hpair.gapPolynomial_eq hr] at he
  apply continuousAt_principalSqrt_real_gap_factor (Real.pi*(n : ℕ)) l u x (by positivity) hx _ _
    ((hnorm _ hxball).trans_lt hepsilon)
  simpa only [ofReal_mul,ofReal_natCast,neg_mul] using he

end NLS.KdV
