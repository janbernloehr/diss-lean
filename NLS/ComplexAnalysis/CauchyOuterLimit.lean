import NLS.ComplexAnalysis.CircleIntegralExteriorNormalization
import Mathlib.Analysis.Normed.Group.Bounded

/-! # The outer Cauchy contour at infinity

A function tending to one at complex infinity has outer Cauchy integral
tending to 2*pi*i. Continuity on sufficiently large circles is explicit.
-/

noncomputable section
open Set Metric Filter Topology Complex
namespace NLS.ComplexAnalysis

/-- A uniform limit at complex infinity gives the Cauchy outer-circle constant. -/
theorem tendsto_outerCircle_cauchy_of_limit_one (f : ℂ → ℂ) (x : ℂ)
    (hf : Tendsto f (Bornology.cobounded ℂ) (𝓝 1))
    (hc : ∀ᶠ R : ℝ in atTop, ContinuousOn f (sphere (0:ℂ) R)) :
    Tendsto (fun R : ℝ => ∮ z in C(0,R), f z/(z-x)) atTop (𝓝 (2*(Real.pi:ℂ)*I)) := by
  let F : ℝ → ℂ → ℂ := fun _ z => I*f z/(x-z)
  have hcont : ∀ᶠ R : ℝ in atTop, ContinuousOn (F R) (sphere (0:ℂ) R) := by
    filter_upwards [hc,eventually_gt_atTop ‖x‖] with R hR hx
    apply (continuousOn_const.mul hR).div (continuousOn_const.sub continuousOn_id)
    intro z hz hzero
    have he : x=z := sub_eq_zero.mp hzero
    have hnorm : ‖z‖=R := by simpa only [mem_sphere,dist_zero_right] using hz
    rw [← he] at hnorm
    linarith
  have herr : ∀ ε : ℝ, 0 < ε → ∀ᶠ R : ℝ in atTop, ∀ z ∈ sphere (0:ℂ) R,
      ‖(x-z)*F R z/I-1‖ ≤ ε := by
    intro ε hε
    have hu : ∀ᶠ z in Bornology.cobounded ℂ, ‖f z-1‖<ε := by
      simpa only [dist_eq_norm] using (Metric.tendsto_nhds.mp hf ε hε)
    have hb : Bornology.IsBounded {z : ℂ | ‖f z-1‖<ε}ᶜ := Bornology.isBounded_compl_iff.mpr hu
    obtain ⟨B,hB⟩ := hb.exists_norm_le
    filter_upwards [eventually_gt_atTop (max B ‖x‖)] with R hR
    intro z hz
    have hnorm : ‖z‖=R := by simpa only [mem_sphere,dist_zero_right] using hz
    have hn : x-z ≠ 0 := by
      intro he
      have heq := sub_eq_zero.mp he
      rw [← heq] at hnorm
      linarith [le_max_right B ‖x‖]
    have hg : ‖f z-1‖<ε := by
      by_contra hg
      have hBz := hB z hg
      rw [hnorm] at hBz
      linarith [le_max_left B ‖x‖]
    have he : (x-z)*F R z/I = f z := by
      unfold F
      field_simp
    rw [he]
    exact hg.le
  have hlim := (tendsto_circleIntegral_of_pole_relative_error x id F tendsto_id hcont herr).const_mul I
  have hlim' : Tendsto (fun R : ℝ => I*(∮ z in C(0,R), F R z)) atTop (𝓝 (2*(Real.pi:ℂ)*I)) := by
    simpa only [id_eq,mul_comm I (2*(Real.pi:ℂ))] using hlim
  apply hlim'.congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with R hR
  rw [← circleIntegral.integral_const_mul]
  apply circleIntegral.integral_congr hR
  intro z _
  change I * (I*f z/(x-z)) = f z/(z-x)
  rw [show x-z = -(z-x) by ring,div_neg,div_eq_mul_inv]
  calc
    I * -(I * f z * (z-x)⁻¹) = -(I*I)*(f z*(z-x)⁻¹) := by ring
    _ = f z/(z-x) := by simp [div_eq_mul_inv]

end NLS.ComplexAnalysis
