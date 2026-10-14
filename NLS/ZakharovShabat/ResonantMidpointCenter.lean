import NLS.ZakharovShabat.ResonantMidpointTaylor

/-!
# Midpoint comparison with the resonant diagonal center

Subtracting two root equations controls the sum of their residuals.
A counted double root uses the vanishing determinant derivative instead.
The diagonal Taylor estimate then bounds the midpoint-center error by
the full off-diagonal product, rather than its square root.
-/

noncomputable section
open Set Metric Complex
namespace NLS.ZakharovShabat

/-- A bounded strip function has a derivative bound on the refined disk. -/
theorem norm_deriv_strip_function_le (n : ℤ) (b : ℂ → ℂ) (M : ℝ)
    (hb : AnalyticOnNhd ℂ b (resonantStrip n))
    (hM : ∀ z ∈ resonantStrip n, ‖b z‖ ≤ M)
    (x : ℂ) (hx : x ∈ refinedResonantDisk n) :
    ‖deriv b x‖ ≤ (4*Real.pi⁻¹)*M := by
  have hball := closedBall_refined_point_subset_strip n x hx
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity : 0 < Real.pi/4)
    (hb.differentiableOn.diffContOnCl_ball hball)
    (fun z hz => hM z (hball (sphere_subset_closedBall hz)))
  convert h using 1
  field_simp

/-- The sum of the two diagonal residuals gains one full product factor.
The derivative premise covers a counted double root. -/
theorem norm_resonant_root_residual_sum_le (n : ℤ) (a b : ℂ → ℂ) (M : ℝ)
    (ha : AnalyticOnNhd ℂ a (resonantStrip n))
    (hab : ∀ z ∈ resonantStrip n, ‖a z‖ ≤ Real.pi/32)
    (hb : AnalyticOnNhd ℂ b (resonantStrip n))
    (hM : ∀ z ∈ resonantStrip n, ‖b z‖ ≤ M)
    (x y : ℂ) (hx : x ∈ refinedResonantDisk n) (hy : y ∈ refinedResonantDisk n)
    (hx0 : (x-(Real.pi:ℂ)*n-a x)^2 = b x)
    (hy0 : (y-(Real.pi:ℂ)*n-a y)^2 = b y)
    (hdouble : x = y → deriv (fun z => (z-(Real.pi:ℂ)*n-a z)^2-b z) x = 0) :
    ‖(x-(Real.pi:ℂ)*n-a x)+(y-(Real.pi:ℂ)*n-a y)‖ ≤ (32/7:ℝ)*Real.pi⁻¹*M := by
  let g := fun z : ℂ => z-(Real.pi:ℂ)*n-a z
  have hK := norm_deriv_strip_function_le n b M hb hM
  have hdiff : ‖b x-b y‖ ≤ ((4*Real.pi⁻¹)*M)*‖x-y‖ :=
    Convex.norm_image_sub_le_of_norm_deriv_le
      (fun z hz => (hb z (refinedResonantDisk_subset_strip n hz)).differentiableAt)
      hK (convex_ball _ _) hy hx
  have ha' := norm_diagonal_sub_le_on_refined_disk n a ha hab x y hx hy
  by_cases hxy : x = y
  · subst y
    have hda := (ha x (refinedResonantDisk_subset_strip n hx)).differentiableAt.hasDerivAt
    have hdb := (hb x (refinedResonantDisk_subset_strip n hx)).differentiableAt.hasDerivAt
    have hd := ((((hasDerivAt_id x).sub_const ((Real.pi:ℂ)*n)).sub hda).pow 2).sub hdb
    have he : 2*g x*(1-deriv a x) = deriv b x := by
      have he := hdouble rfl
      have hd' : deriv (fun z => (z-(Real.pi:ℂ)*n-a z)^2-b z) x =
          2*g x*(1-deriv a x)-deriv b x := by
        convert! hd.deriv using 1; simp only [g,Pi.sub_apply,id_eq,Nat.reduceSub,pow_one,Nat.cast_ofNat]
      rw [hd'] at he
      exact sub_eq_zero.mp he
    have hlo : (7/8:ℝ) ≤ ‖1-deriv a x‖ := by
      have ht := norm_le_norm_sub_add (1:ℂ) (deriv a x)
      have ha1 := norm_deriv_le_on_refined_disk n a ha hab x hx
      norm_num only [norm_one] at ht
      linarith
    have hn := congrArg norm he
    simp only [norm_mul,norm_ofNat] at hn
    have hb1 := hK x hx
    have hm := mul_le_mul_of_nonneg_left hlo (by positivity : 0 ≤ 2*‖g x‖)
    change ‖g x+g x‖ ≤ _
    rw [← two_mul,norm_mul]
    norm_num only [norm_ofNat]
    nlinarith
  · have hgap : 0 < ‖x-y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
    have he : (g x+g y)*(g x-g y) = b x-b y := by dsimp [g]; linear_combination hx0-hy0
    have hlo : (7/8:ℝ)*‖x-y‖ ≤ ‖g x-g y‖ := by
      have he' : x-y = (g x-g y)+(a x-a y) := by dsimp [g]; ring
      have ht := norm_add_le (g x-g y) (a x-a y)
      rw [← he'] at ht
      linarith
    have hn : ‖g x+g y‖*‖g x-g y‖ ≤ ((4*Real.pi⁻¹)*M)*‖x-y‖ := by
      rw [← norm_mul,he]
      exact hdiff
    have hm := mul_le_mul_of_nonneg_left hlo (norm_nonneg (g x+g y))
    change ‖g x+g y‖ ≤ _
    nlinarith

/-- The actual midpoint differs from the diagonal center by a full off-diagonal
product bound, including a repeated root. -/
theorem norm_resonant_midpoint_sub_center_le (n : ℤ) (a b : ℂ → ℂ) (M : ℝ)
    (ha : AnalyticOnNhd ℂ a (resonantStrip n))
    (hab : ∀ z ∈ resonantStrip n, ‖a z‖ ≤ Real.pi/32)
    (hb : AnalyticOnNhd ℂ b (resonantStrip n))
    (hM : ∀ z ∈ resonantStrip n, ‖b z‖ ≤ M)
    (x y ζ : ℂ) (hx : x ∈ refinedResonantDisk n) (hy : y ∈ refinedResonantDisk n)
    (hζ : ζ ∈ refinedResonantDisk n) (hfix : ζ = (Real.pi:ℂ)*n+a ζ)
    (hx0 : (x-(Real.pi:ℂ)*n-a x)^2 = b x)
    (hy0 : (y-(Real.pi:ℂ)*n-a y)^2 = b y)
    (hdouble : x = y → deriv (fun z => (z-(Real.pi:ℂ)*n-a z)^2-b z) x = 0) :
    ‖(x+y)/2-ζ‖ ≤ (8*Real.pi⁻¹)*M := by
  let t := (x+y)/2
  let g := fun z : ℂ => z-(Real.pi:ℂ)*n-a z
  have ht := midpoint_mem_refinedResonantDisk n x y hx hy
  have hpos : 0 ≤ M := (norm_nonneg (b x)).trans (hM x (refinedResonantDisk_subset_strip n hx))
  have hgap : ‖x-y‖^2 ≤ 6*M := by
    apply norm_gap_sq_le_of_residual_bounds ((Real.pi:ℂ)*n) x y a M
      (norm_diagonal_sub_le_on_refined_disk n a ha hab x y hx hy)
    · rw [← norm_pow,hx0]; exact hM x (refinedResonantDisk_subset_strip n hx)
    · rw [← norm_pow,hy0]; exact hM y (refinedResonantDisk_subset_strip n hy)
  have hsum := norm_resonant_root_residual_sum_le n a b M ha hab hb hM x y hx hy hx0 hy0 hdouble
  have herr := norm_diagonal_midpoint_error_le n a ha hab x y hx hy
  have he : g t = (g x+g y)/2- (a t-(a x+a y)/2) := by dsimp [g,t]; ring
  have hgt : ‖g t‖ ≤ (37/7:ℝ)*Real.pi⁻¹*M := by
    have htri := norm_sub_le ((g x+g y)/2) (a t-(a x+a y)/2)
    rw [← he,norm_div] at htri
    norm_num only [norm_ofNat] at htri
    have hgap' := mul_le_mul_of_nonneg_left hgap (by positivity : 0 ≤ Real.pi⁻¹/2)
    change ‖g x+g y‖ ≤ _ at hsum
    change ‖a t-(a x+a y)/2‖ ≤ _ at herr
    nlinarith
  have hlip := norm_diagonal_sub_le_on_refined_disk n a ha hab t ζ ht hζ
  have he' : t-ζ = g t+(a t-a ζ) := by dsimp [g]; linear_combination -hfix
  have htri := norm_add_le (g t) (a t-a ζ)
  rw [← he'] at htri
  change ‖t-ζ‖ ≤ _
  have hp : 0 ≤ Real.pi⁻¹*M := mul_nonneg (inv_nonneg.mpr Real.pi_pos.le) hpos
  nlinarith

end NLS.ZakharovShabat
