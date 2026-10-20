import NLS.ComplexAnalysis.DiscBounds
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # Disc bounds after removing two nearby roots

A quadratic factor comparison and the maximum modulus principle control the entire quotient even when the removed roots coincide.
-/

noncomputable section
open Complex Set Metric
namespace NLS.ComplexAnalysis

/-- Two roots within half a contour radius give a uniform lower bound
for their quadratic factor on that contour, including coincident roots. -/
theorem sq_radius_le_four_mul_norm_two_root_factor
    (a b c z : ℂ) (r ε : ℝ) (hr : 0 < r) (hεr : ε ≤ r/2)
    (ha : ‖a-c‖ ≤ ε) (hb : ‖b-c‖ ≤ ε) (hz : ‖z-c‖ = r) :
    r^2/4 ≤ ‖(z-a)*(z-b)‖ := by
  have hza : r/2 ≤ ‖z-a‖ := by
    have h := norm_sub_le_norm_sub_add_norm_sub z a c
    rw [hz] at h
    linarith
  have hzb : r/2 ≤ ‖z-b‖ := by
    have h := norm_sub_le_norm_sub_add_norm_sub z b c
    rw [hz] at h
    linarith
  rw [norm_mul]
  have h := mul_le_mul hza hzb (by linarith : 0 ≤ r/2) (norm_nonneg (z-a))
  nlinarith

/-- Perturbing two roots from a common center controls their quadratic
factor on a fixed circle without dividing by the gap length. -/
theorem norm_two_root_factor_sub_center_sq_le
    (a b c z : ℂ) (r ε : ℝ) (hε : 0 ≤ ε)
    (ha : ‖a-c‖ ≤ ε) (hb : ‖b-c‖ ≤ ε) (hz : ‖z-c‖ = r) :
    ‖(z-a)*(z-b)-(z-c)^2‖ ≤ 2*r*ε+ε^2 := by
  have he : (z-a)*(z-b)-(z-c)^2 = -(z-c)*((a-c)+(b-c))+(a-c)*(b-c) := by ring
  have hr : 0 ≤ r := hz ▸ norm_nonneg (z-c)
  rw [he]
  calc
    _ ≤ ‖-(z-c)*((a-c)+(b-c))‖+‖(a-c)*(b-c)‖ := norm_add_le _ _
    _ = r*‖(a-c)+(b-c)‖+‖a-c‖*‖b-c‖ := by rw [norm_mul,norm_mul,norm_neg,hz]
    _ ≤ r*(ε+ε)+ε*ε := add_le_add
      (mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add ha hb)) hr)
      (mul_le_mul ha hb (norm_nonneg _) hε)
    _ = _ := by ring

/-- Removing two nearby roots preserves a contour comparison throughout
the disc. No separation of the two removed roots is required. -/
theorem norm_two_root_quotient_sub_le_on_closedDisc
    (F F₀ Q Q₀ : ℂ → ℂ) (a b c : ℂ) (r ε A B : ℝ)
    (hr : 0 < r) (hε : 0 ≤ ε) (hεr : ε ≤ r/2) (hB : 0 ≤ B)
    (ha : ‖a-c‖ ≤ ε) (hb : ‖b-c‖ ≤ ε)
    (hQ : Differentiable ℂ Q) (hQ₀ : Differentiable ℂ Q₀)
    (hF : ∀ z, F z = (z-a)*(z-b)*Q z)
    (hF₀ : ∀ z, F₀ z = (z-c)^2*Q₀ z)
    (herror : ∀ z ∈ sphere c r, ‖F z-F₀ z‖ ≤ A)
    (hmodel : ∀ z ∈ sphere c r, ‖Q₀ z‖ ≤ B)
    (z : ℂ) (hz : ‖z-c‖ ≤ r) :
    ‖Q z-Q₀ z‖ ≤ 4*(A+B*(2*r*ε+ε^2))/r^2 := by
  apply norm_le_of_sphere_bound (hQ.sub hQ₀) c hr _ ?_ hz
  intro w hw
  have hwr : ‖w-c‖ = r := by simpa only [mem_sphere,dist_eq_norm] using hw
  have hlo := sq_radius_le_four_mul_norm_two_root_factor a b c w r ε hr hεr ha hb hwr
  have hfactor := norm_two_root_factor_sub_center_sq_le a b c w r ε hε ha hb hwr
  have hid : (Q w-Q₀ w)*((w-a)*(w-b)) =
      F w-F₀ w-Q₀ w*((w-a)*(w-b)-(w-c)^2) := by
    rw [hF w,hF₀ w]
    ring
  have hmul : ‖Q w-Q₀ w‖*(r^2/4) ≤ A+B*(2*r*ε+ε^2) := by
    calc
      _ ≤ ‖Q w-Q₀ w‖*‖(w-a)*(w-b)‖ := mul_le_mul_of_nonneg_left hlo (norm_nonneg _)
      _ = ‖F w-F₀ w-Q₀ w*((w-a)*(w-b)-(w-c)^2)‖ := by rw [← norm_mul,hid]
      _ ≤ ‖F w-F₀ w‖+‖Q₀ w*((w-a)*(w-b)-(w-c)^2)‖ := norm_sub_le _ _
      _ ≤ A+B*(2*r*ε+ε^2) := by
        rw [norm_mul]
        exact add_le_add (herror w hw) (mul_le_mul (hmodel w hw) hfactor (norm_nonneg _) hB)
  calc
    _ ≤ (A+B*(2*r*ε+ε^2))/(r^2/4) := (le_div_iff₀ (by positivity)).mpr hmul
    _ = _ := by ring

end NLS.ComplexAnalysis
