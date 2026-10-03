import NLS.ZakharovShabat.FreeHalfDiscGeometry

/-! # Free-circle separation for the G.7 contours -/

noncomputable section
open Set Metric Complex
namespace NLS.ZakharovShabat

/-- Circles of radius at most π/2 stay at least that radius from every free center. -/
theorem freeCircle_separated (r : ℝ) (hr : r ≤ Real.pi/2) (n : ℤ) (z : ℂ)
    (hz : z ∈ sphere ((Real.pi : ℂ)*(n : ℂ)) r) :
    ∀ m : ℤ, r ≤ ‖z-(Real.pi : ℂ)*(m : ℂ)‖ := by
  have hzn : ‖z-(Real.pi : ℂ)*(n : ℂ)‖ = r := by
    simpa only [mem_sphere,dist_eq_norm] using hz
  intro m
  by_cases hm : m = n
  · simpa [hm] using hzn.ge
  have hmn : (1 : ℝ) ≤ |((m-n : ℤ) : ℝ)| := by
    exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hm)
  have hcenters : Real.pi ≤ ‖(Real.pi : ℂ)*(m : ℂ)-(Real.pi : ℂ)*(n : ℂ)‖ := by
    rw [norm_free_center_sub]
    nlinarith [Real.pi_pos]
  have htriangle : ‖(Real.pi : ℂ)*(m : ℂ)-(Real.pi : ℂ)*(n : ℂ)‖ ≤
      ‖(Real.pi : ℂ)*(m : ℂ)-z‖+‖z-(Real.pi : ℂ)*(n : ℂ)‖ := by
    calc
      _ = ‖((Real.pi : ℂ)*(m : ℂ)-z)+(z-(Real.pi : ℂ)*(n : ℂ))‖ := by congr 1; ring
      _ ≤ _ := norm_add_le _ _
  rw [norm_sub_rev ((Real.pi : ℂ)*(m : ℂ)) z,hzn] at htriangle
  linarith

/-- Each free-centered radius-r circle lies in the horizontal strip of height r. -/
theorem freeCircle_im_le (r : ℝ) (n : ℤ) (z : ℂ)
    (hz : z ∈ sphere ((Real.pi : ℂ)*(n : ℂ)) r) : |z.im| ≤ r := by
  have h := Complex.abs_im_le_norm (z-(Real.pi : ℂ)*(n : ℂ))
  have hzn : ‖z-(Real.pi : ℂ)*(n : ℂ)‖ = r := by simpa only [mem_sphere,dist_eq_norm] using hz
  simpa [hzn] using h

end NLS.ZakharovShabat
