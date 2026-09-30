import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Normalization from a uniform exterior pole asymptotic

A contour integrand asymptotic to `i/(w-z)` has integral tending to
`2π` on circles whose radii tend to infinity. Uniform relative error
supplies a pointwise error of order `1/R`; the circle length cancels
that decay. This is the exterior integral step in Lemma 12.11.
-/

noncomputable section
open Set Complex Filter Topology Metric
namespace NLS.ComplexAnalysis

/-- The pole with the orientation used for the psi numerators has raw
circle integral `2π`. -/
theorem circleIntegral_I_div_sub_eq_two_pi (w : ℂ) (R : ℝ)
    (hw : ‖w‖ < R) :
    (∮ z in C(0,R), I/(w-z)) = (2*Real.pi : ℂ) := by
  have he : (fun z : ℂ => I/(w-z)) = fun z => (-I)*(z-w)⁻¹ := by
    funext z
    rw [show w-z = -(z-w) by ring, div_eq_mul_inv, inv_neg]
    ring
  rw [he, circleIntegral.integral_const_mul,
    circleIntegral.integral_sub_inv_of_mem_ball (by simpa only [mem_ball, dist_zero_right] using hw)]
  calc
    (-I)*(2*Real.pi*I) = -(2*Real.pi)*(I*I) := by ring
    _ = _ := by simp

/-- Uniform relative error to the pole implies the correctly oriented
large-circle integral limit, for any escaping radius family. -/
theorem tendsto_circleIntegral_of_pole_relative_error {α : Type*} {l : Filter α}
    (w : ℂ) (R : α → ℝ) (F : α → ℂ → ℂ)
    (hR : Tendsto R l atTop)
    (hcont : ∀ᶠ i in l, ContinuousOn (F i) (sphere (0 : ℂ) (R i)))
    (herr : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, ∀ z ∈ sphere (0 : ℂ) (R i),
      ‖(w-z)*F i z/I-1‖ ≤ ε) :
    Tendsto (fun i => ∮ z in C(0,R i), F i z) l (𝓝 (2*Real.pi : ℂ)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := ε/(8*Real.pi)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hδε : 4*Real.pi*δ < ε := by
    have he : 4*Real.pi*δ = ε/2 := by
      dsimp only [δ]
      field_simp
      ring
    rw [he]
    linarith
  filter_upwards [hcont, herr δ hδ, hR.eventually_ge_atTop (2*‖w‖+1)] with i hi he hr
  have hRp : 0 < R i := by linarith [norm_nonneg w]
  have hwR : ‖w‖ < R i := by linarith [norm_nonneg w]
  have hsep (z : ℂ) (hz : z ∈ sphere (0 : ℂ) (R i)) : R i/2 ≤ ‖w-z‖ := by
    have hnorm : ‖z‖ = R i := by simpa only [mem_sphere, dist_zero_right] using hz
    have htri : ‖z‖ ≤ ‖w‖+‖w-z‖ := by
      calc
        _ = ‖w-(w-z)‖ := by congr 1; ring
        _ ≤ _ := norm_sub_le _ _
    linarith
  have hne (z : ℂ) (hz : z ∈ sphere (0 : ℂ) (R i)) : w-z ≠ 0 :=
    norm_pos_iff.mp ((half_pos hRp).trans_le (hsep z hz))
  have hpcont : ContinuousOn (fun z : ℂ => I/(w-z)) (sphere (0 : ℂ) (R i)) :=
    continuousOn_const.div (continuousOn_const.sub continuousOn_id) hne
  have hpoint (z : ℂ) (hz : z ∈ sphere (0 : ℂ) (R i)) :
      ‖F i z-I/(w-z)‖ ≤ δ/(R i/2) := by
    have hid : F i z-I/(w-z) = I/(w-z)*((w-z)*F i z/I-1) := by
      field_simp [hne z hz]
    rw [hid, norm_mul, norm_div, norm_I, one_div, ← div_eq_inv_mul]
    exact (div_le_div_of_nonneg_right (he z hz) (norm_nonneg _)).trans
      (div_le_div_of_nonneg_left hδ.le (half_pos hRp) (hsep z hz))
  have hint := circleIntegral.norm_integral_le_of_norm_le_const hRp.le hpoint
  have hbound : 2*Real.pi*R i*(δ/(R i/2)) = 4*Real.pi*δ := by
    field_simp
    ring
  rw [hbound] at hint
  have hpint := circleIntegral_I_div_sub_eq_two_pi w (R i) hwR
  rw [dist_eq_norm, ← hpint, ← circleIntegral.integral_sub
    (hi.circleIntegrable hRp.le) (hpcont.circleIntegrable hRp.le)]
  exact hint.trans_lt hδε

end NLS.ComplexAnalysis
