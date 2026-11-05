import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic

/-! # Endpoint bounds for a quotient by a two-zero root

A nonvanishing deflated unit and a distinct second endpoint give the
inverse-square-root bound required for a primitive's full slit-endpoint
limit. The estimate uses the actual root square and does not choose a
new sign or require a gap-length lower bound uniform in the potential.
-/

noncomputable section
open Set Filter Topology Complex Metric
namespace NLS.ComplexAnalysis

theorem exists_two_zero_root_endpoint_bound
    (N Q R : ℂ → ℂ) (D : Set ℂ) (a b : ℂ) (hab : a ≠ b)
    (hN : ContinuousAt N a) (hQ : ContinuousAt Q a) (hQa : Q a ≠ 0)
    (hroot : ∀ z ∈ D, R z ≠ 0 ∧ R z^2 = (z-a)*(z-b)*Q z) :
    ∃ δ M ε : ℝ, 0 < δ ∧ 0 ≤ M ∧ 0 < ε ∧
      ∀ z ∈ D, ‖z-a‖ ≤ ε →
        ‖(N z/R z)*(Real.sqrt (δ*‖z-a‖) : ℂ)‖ ≤ M := by
  have hqan : 0 < ‖Q a‖ := norm_pos_iff.mpr hQa
  have habn : 0 < ‖a-b‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hab)
  have heN : ∀ᶠ z in 𝓝 a, ‖N z‖ < ‖N a‖+1 :=
    hN.norm.preimage_mem_nhds (Iio_mem_nhds (by linarith))
  have heQ : ∀ᶠ z in 𝓝 a, ‖Q a‖/2 < ‖Q z‖ :=
    hQ.norm.preimage_mem_nhds (Ioi_mem_nhds (by linarith))
  obtain ⟨η,hη,hsmall⟩ := Metric.eventually_nhds_iff.mp (heN.and heQ)
  let δ := ‖a-b‖*‖Q a‖/4
  let ε := min (η/2) (‖a-b‖/2)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hε : 0 < ε := lt_min (by positivity) (by positivity)
  refine ⟨δ,‖N a‖+1,ε,hδ,by positivity,hε,?_⟩
  intro z hz hdist
  have hzη : dist z a < η := by
    rw [dist_eq_norm]
    have hεη : ε ≤ η/2 := min_le_left _ _
    linarith
  have hb := hsmall hzη
  have hsep : ‖a-b‖/2 ≤ ‖z-b‖ := by
    have ht := norm_sub_le_norm_sub_add_norm_sub a z b
    rw [norm_sub_rev a z] at ht
    have hεab : ε ≤ ‖a-b‖/2 := min_le_right _ _
    linarith
  have hprod : (‖a-b‖/2)*(‖Q a‖/2) ≤ ‖z-b‖*‖Q z‖ :=
    mul_le_mul hsep hb.2.le (by positivity) (norm_nonneg _)
  have hRsq : ‖R z‖^2 = ‖z-a‖*‖z-b‖*‖Q z‖ := by
    rw [← norm_pow,(hroot z hz).2,norm_mul,norm_mul]
  have hbound : δ*‖z-a‖ ≤ ‖R z‖^2 := by
    calc
      _ = ‖z-a‖*((‖a-b‖/2)*(‖Q a‖/2)) := by dsimp [δ]; ring
      _ ≤ ‖z-a‖*(‖z-b‖*‖Q z‖) := mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
      _ = _ := by rw [hRsq]; ring
  have hsqrt : Real.sqrt (δ*‖z-a‖) ≤ ‖R z‖ := by
    have he := Real.sq_sqrt (show 0 ≤ δ*‖z-a‖ by positivity)
    nlinarith [Real.sqrt_nonneg (δ*‖z-a‖),norm_nonneg (R z)]
  rw [norm_mul,norm_div,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  calc
    _ ≤ (‖N z‖/‖R z‖)*‖R z‖ := mul_le_mul_of_nonneg_left hsqrt (by positivity)
    _ = ‖N z‖ := div_mul_cancel₀ _ (norm_ne_zero_iff.mpr (hroot z hz).1)
    _ ≤ _ := hb.1.le

end NLS.ComplexAnalysis
