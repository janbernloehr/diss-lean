import NLS.ZakharovShabat.ResonantDiagonalCenter

/-!
# Diagonal Taylor bounds for periodic midpoints

Cauchy estimates on nested disks bound the second spectral derivative.
The first-order remainders at two endpoints have cancelling linear terms,
so averaging introduces a squared-gap error, without a reality assumption.
-/

noncomputable section
open Set Metric Complex
namespace NLS.ZakharovShabat

/-- A larger disk leaves room for the second Cauchy estimate. -/
theorem norm_deriv_diagonal_le_three_eighths (n : ℤ) (a : ℂ → ℂ)
    (ha : AnalyticOnNhd ℂ a (resonantStrip n))
    (hb : ∀ z ∈ resonantStrip n, ‖a z‖ ≤ Real.pi/32)
    (x : ℂ) (hx : x ∈ ball ((Real.pi:ℂ)*n) (3*Real.pi/8)) :
    ‖deriv a x‖ ≤ 1/4 := by
  have hball : closedBall x (Real.pi/8) ⊆ resonantStrip n := by
    intro z hz
    apply closedBall_subset_resonantStrip n le_rfl
    apply mem_closedBall.mpr
    have hzx := mem_closedBall.mp hz
    have hxc := mem_ball.mp hx
    exact (dist_triangle z x _).trans (by linarith)
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity : 0 < Real.pi/8)
    (ha.differentiableOn.diffContOnCl_ball hball)
    (fun z hz => hb z (hball (sphere_subset_closedBall hz)))
  convert h using 1
  field_simp
  ring

/-- The second derivative is bounded throughout the refined disk. -/
theorem norm_second_deriv_diagonal_le (n : ℤ) (a : ℂ → ℂ)
    (ha : AnalyticOnNhd ℂ a (resonantStrip n))
    (hb : ∀ z ∈ resonantStrip n, ‖a z‖ ≤ Real.pi/32)
    (x : ℂ) (hx : x ∈ refinedResonantDisk n) :
    ‖deriv (deriv a) x‖ ≤ 2*Real.pi⁻¹ := by
  have hball : closedBall x (Real.pi/8) ⊆ ball ((Real.pi:ℂ)*n) (3*Real.pi/8) := by
    intro z hz
    apply mem_ball.mpr
    have hzx := mem_closedBall.mp hz
    have hxc : dist x ((Real.pi:ℂ)*n) < Real.pi/4 := hx
    exact (dist_triangle z x _).trans_lt (by linarith)
  have hstrip : ball ((Real.pi:ℂ)*n) (3*Real.pi/8) ⊆ resonantStrip n :=
    ball_subset_closedBall.trans (closedBall_subset_resonantStrip n (by linarith [Real.pi_pos]))
  have hda : AnalyticOnNhd ℂ (deriv a) (resonantStrip n) := fun z hz => (ha z hz).deriv
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity : 0 < Real.pi/8)
    (hda.differentiableOn.diffContOnCl_ball (hball.trans hstrip))
    (fun z hz => norm_deriv_diagonal_le_three_eighths n a ha hb z (hball (sphere_subset_closedBall hz)))
  convert h using 1
  field_simp
  ring

/-- The spectral derivative is Lipschitz on the refined disk. -/
theorem norm_deriv_diagonal_sub_le (n : ℤ) (a : ℂ → ℂ)
    (ha : AnalyticOnNhd ℂ a (resonantStrip n))
    (hb : ∀ z ∈ resonantStrip n, ‖a z‖ ≤ Real.pi/32)
    (x y : ℂ) (hx : x ∈ refinedResonantDisk n) (hy : y ∈ refinedResonantDisk n) :
    ‖deriv a x-deriv a y‖ ≤ (2*Real.pi⁻¹)*‖x-y‖ :=
  Convex.norm_image_sub_le_of_norm_deriv_le
    (fun z hz => (ha z (refinedResonantDisk_subset_strip n hz)).deriv.differentiableAt)
    (norm_second_deriv_diagonal_le n a ha hb) (convex_ball _ _) hy hx

/-- A first-order remainder bound holds on every complex segment in the disk. -/
theorem norm_diagonal_taylor_remainder_le (n : ℤ) (a : ℂ → ℂ)
    (ha : AnalyticOnNhd ℂ a (resonantStrip n))
    (hb : ∀ z ∈ resonantStrip n, ‖a z‖ ≤ Real.pi/32)
    (x y : ℂ) (hx : x ∈ refinedResonantDisk n) (hy : y ∈ refinedResonantDisk n) :
    ‖a x-a y-deriv a y*(x-y)‖ ≤ (2*Real.pi⁻¹)*‖x-y‖^2 := by
  let f : ℂ → ℂ := fun z => a z-a y-deriv a y*(z-y)
  have hs : segment ℝ y x ⊆ refinedResonantDisk n := (convex_ball _ _).segment_subset hy hx
  have hc : segment ℝ y x ⊆ closedBall y ‖x-y‖ :=
    (convex_closedBall y ‖x-y‖).segment_subset (mem_closedBall_self (norm_nonneg _))
      (by simp only [mem_closedBall,dist_eq_norm,le_refl])
  have hf (z : ℂ) (hz : z ∈ segment ℝ y x) : HasDerivAt f (deriv a z-deriv a y) z := by
    simpa only [mul_one, f, Pi.sub_apply, id_eq] using!
      (((ha z (refinedResonantDisk_subset_strip n (hs hz))).differentiableAt.hasDerivAt.sub_const (a y)).sub
        (((hasDerivAt_id z).sub_const y).const_mul (deriv a y)))
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun z hz => (hf z hz).differentiableAt)
    (fun z hz => (hf z hz).deriv ▸
      (norm_deriv_diagonal_sub_le n a ha hb z y (hs hz) hy).trans
        (mul_le_mul_of_nonneg_left (show ‖z-y‖ ≤ ‖x-y‖ by simpa only [mem_closedBall,dist_eq_norm] using hc hz) (by positivity)))
    (convex_segment y x) (left_mem_segment ℝ y x) (right_mem_segment ℝ y x)
  simpa only [f,sub_self,mul_zero,sub_zero,pow_two,mul_assoc] using h

/-- The arithmetic midpoint remains in the refined disk. -/
theorem midpoint_mem_refinedResonantDisk (n : ℤ) (x y : ℂ)
    (hx : x ∈ refinedResonantDisk n) (hy : y ∈ refinedResonantDisk n) :
    (x+y)/2 ∈ refinedResonantDisk n := by
  have h := (convex_ball ((Real.pi:ℂ)*n) (Real.pi/4)).midpoint_mem hx hy
  simpa only [midpoint_eq_smul_add, smul_eq_mul, Complex.real_smul, invOf_eq_inv,
    Complex.ofReal_inv, Complex.ofReal_ofNat, div_eq_inv_mul, refinedResonantDisk] using h

/-- Linear terms cancel between the two endpoints, leaving a squared-gap error. -/
theorem norm_diagonal_midpoint_error_le (n : ℤ) (a : ℂ → ℂ)
    (ha : AnalyticOnNhd ℂ a (resonantStrip n))
    (hb : ∀ z ∈ resonantStrip n, ‖a z‖ ≤ Real.pi/32)
    (x y : ℂ) (hx : x ∈ refinedResonantDisk n) (hy : y ∈ refinedResonantDisk n) :
    ‖a ((x+y)/2)-(a x+a y)/2‖ ≤ (Real.pi⁻¹/2)*‖x-y‖^2 := by
  let t := (x+y)/2
  have ht := midpoint_mem_refinedResonantDisk n x y hx hy
  have hx' := norm_diagonal_taylor_remainder_le n a ha hb x t hx ht
  have hy' := norm_diagonal_taylor_remainder_le n a ha hb y t hy ht
  have hxt : x-t = (x-y)/2 := by dsimp [t]; ring
  have hyt : y-t = -(x-y)/2 := by dsimp [t]; ring
  have hnx : ‖x-t‖ = ‖x-y‖/2 := by rw [hxt,norm_div]; norm_num
  have hny : ‖y-t‖ = ‖x-y‖/2 := by rw [hyt,norm_div,norm_neg]; norm_num
  have he : a t-(a x+a y)/2 =
      -((a x-a t-deriv a t*(x-t))+(a y-a t-deriv a t*(y-t)))/2 := by dsimp [t]; ring
  rw [he,norm_div,norm_neg]
  norm_num only [norm_ofNat]
  have hb' := (norm_add_le (a x-a t-deriv a t*(x-t))
    (a y-a t-deriv a t*(y-t))).trans (add_le_add hx' hy')
  rw [hnx,hny] at hb'
  nlinarith

end NLS.ZakharovShabat
