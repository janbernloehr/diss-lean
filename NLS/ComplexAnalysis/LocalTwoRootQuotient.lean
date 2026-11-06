import NLS.ComplexAnalysis.TwoRootQuotientDiscBound
import NLS.ComplexAnalysis.CauchyFiniteHoles

/-! # Removing two roots on a local analytic disc

The filled divided difference removes two zeros, including a double zero.
Maximum modulus then controls the quotient on the same closed disc. Only
analyticity near that disc is needed; no entire extension is assumed.
-/
noncomputable section
set_option autoImplicit false
open Complex Set Metric
namespace NLS.ComplexAnalysis

/-- The twice filled divided difference, also defined when the roots coincide. -/
def twoRootDeflation (f : ℂ → ℂ) (a b : ℂ) : ℂ → ℂ :=
  dslope (dslope f a) b

theorem analyticOnNhd_twoRootDeflation (f : ℂ → ℂ) (U : Set ℂ) (a b : ℂ)
    (hf : AnalyticOnNhd ℂ f U) (ha : a ∈ U) (hb : b ∈ U) :
    AnalyticOnNhd ℂ (twoRootDeflation f a b) U :=
  analyticOnNhd_dslope_of_analytic _ U b
    (analyticOnNhd_dslope_of_analytic f U a hf ha) hb

/-- Exact deflation needs the derivative to vanish only at a repeated root. -/
theorem twoRootDeflation_factor (f : ℂ → ℂ) (a b : ℂ)
    (ha : f a = 0) (hb : f b = 0) (hab : a = b → deriv f a = 0) (z : ℂ) :
    f z = (z-a)*(z-b)*twoRootDeflation f a b z := by
  have hd : dslope f a b = 0 := by
    by_cases he : b = a
    · subst b
      simpa only [dslope_same] using hab rfl
    · rw [dslope_of_ne f he, slope_def_field, ha, hb]
      simp
  have h₁ := sub_smul_dslope f a z
  have h₂ := sub_smul_dslope (dslope f a) b z
  simp only [smul_eq_mul, ha, hd, sub_zero] at h₁ h₂
  change (z-b)*twoRootDeflation f a b z = dslope f a z at h₂
  rw [← h₁, ← h₂]
  ring

/-- Local maximum modulus, including the boundary of the disc. -/
theorem norm_le_of_sphere_bound_of_analyticOnNhd {f : ℂ → ℂ} (c : ℂ)
    {R : ℝ} (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall c R)) (B : ℝ)
    (hb : ∀ w ∈ sphere c R, ‖f w‖ ≤ B) {z : ℂ} (hz : ‖z-c‖ ≤ R) :
    ‖f z‖ ≤ B := by
  have hd : DiffContOnCl ℂ f (ball c R) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball c hR.ne']
    exact hf.differentiableOn
  apply Complex.norm_le_of_forall_mem_frontier_norm_le (isBounded_ball (x := c) (r := R)) hd
  · intro w hw
    rw [frontier_ball _ hR.ne'] at hw
    exact hb w hw
  · rw [closure_ball c hR.ne']
    simpa only [mem_closedBall, dist_eq_norm] using hz

/-- A two-root quotient comparison requires only local analytic quotients
and boundary factorization, and remains valid at a closed gap. -/
theorem norm_twoRootQuotient_sub_le_of_analyticOnNhd
    (F F₀ Q Q₀ : ℂ → ℂ) (a b c : ℂ) (r ε A B : ℝ)
    (hr : 0 < r) (hε : 0 ≤ ε) (hεr : ε ≤ r/2) (hB : 0 ≤ B)
    (ha : ‖a-c‖ ≤ ε) (hb : ‖b-c‖ ≤ ε)
    (hQ : AnalyticOnNhd ℂ Q (closedBall c r))
    (hQ₀ : AnalyticOnNhd ℂ Q₀ (closedBall c r))
    (hF : ∀ z ∈ sphere c r, F z = (z-a)*(z-b)*Q z)
    (hF₀ : ∀ z ∈ sphere c r, F₀ z = (z-c)^2*Q₀ z)
    (herror : ∀ z ∈ sphere c r, ‖F z-F₀ z‖ ≤ A)
    (hmodel : ∀ z ∈ sphere c r, ‖Q₀ z‖ ≤ B)
    (z : ℂ) (hz : ‖z-c‖ ≤ r) :
    ‖Q z-Q₀ z‖ ≤ 4*(A+B*(2*r*ε+ε^2))/r^2 := by
  apply norm_le_of_sphere_bound_of_analyticOnNhd c hr (hQ.sub hQ₀) _ ?_ hz
  intro w hw
  have hwr : ‖w-c‖ = r := by simpa only [mem_sphere, dist_eq_norm] using hw
  have hlo := sq_radius_le_four_mul_norm_two_root_factor a b c w r ε hr hεr ha hb hwr
  have hfactor := norm_two_root_factor_sub_center_sq_le a b c w r ε hε ha hb hwr
  have hid : (Q w-Q₀ w)*((w-a)*(w-b)) =
      F w-F₀ w-Q₀ w*((w-a)*(w-b)-(w-c)^2) := by
    rw [hF w hw, hF₀ w hw]
    ring
  have hmul : ‖Q w-Q₀ w‖*(r^2/4) ≤ A+B*(2*r*ε+ε^2) := by
    calc
      _ ≤ ‖Q w-Q₀ w‖*‖(w-a)*(w-b)‖ := mul_le_mul_of_nonneg_left hlo (norm_nonneg _)
      _ = ‖F w-F₀ w-Q₀ w*((w-a)*(w-b)-(w-c)^2)‖ := by rw [← norm_mul, hid]
      _ ≤ ‖F w-F₀ w‖+‖Q₀ w*((w-a)*(w-b)-(w-c)^2)‖ := norm_sub_le _ _
      _ ≤ A+B*(2*r*ε+ε^2) := by
        rw [norm_mul]
        exact add_le_add (herror w hw)
          (mul_le_mul (hmodel w hw) hfactor (norm_nonneg _) hB)
  calc
    _ ≤ (A+B*(2*r*ε+ε^2))/(r^2/4) := (le_div_iff₀ (by positivity)).mpr hmul
    _ = _ := by ring

end NLS.ComplexAnalysis
