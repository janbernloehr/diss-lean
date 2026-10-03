import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Transferring first-order coefficients through a quadratic identity -/
noncomputable section
open Complex Filter Topology
namespace NLS.ComplexAnalysis

/-- Two normalized functions with the same square to first order have the
same first-order coefficient. The common limit one fixes the square-root sign. -/
theorem tendsto_scaled_sub_one_of_sq_sub {α : Type*} {l : Filter α}
    (u v a : α → ℂ) (M : ℂ) (hu : Tendsto u l (𝓝 1)) (hv : Tendsto v l (𝓝 1))
    (hM : Tendsto (fun i => a i * (u i - 1)) l (𝓝 M))
    (hsq : Tendsto (fun i => a i * (v i ^ 2 - u i ^ 2)) l (𝓝 0)) :
    Tendsto (fun i => a i * (v i - 1)) l (𝓝 M) := by
  have hsum : Tendsto (fun i => v i + u i) l (𝓝 (2 : ℂ)) := by
    simpa only [one_add_one_eq_two] using hv.add hu
  have hquot : Tendsto (fun i => a i * (v i ^ 2 - u i ^ 2)/(v i + u i)) l (𝓝 0) := by
    simpa only [Pi.div_apply, zero_div] using! hsq.div hsum (by norm_num : (2 : ℂ) ≠ 0)
  have h := hquot.add hM
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [hsum.eventually_ne (by norm_num : (2 : ℂ) ≠ 0)] with i hi
  field_simp
  ring

end NLS.ComplexAnalysis
