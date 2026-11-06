import NLS.KdV.HillAnalytic
import NLS.SequenceSpaces.TwoPoleReciprocalEnvelope

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal Classical

namespace NLS.KdV



private theorem hillFreeBoundaryGreen_symbol_bound (n : ℕ) (hn : 1 ≤ n) (r : ℤ)
    (z : ℂ) (hz : z ∈ reducedHillStrip n) (k : ℤ) :
    ‖if k.natAbs=n then (0 : ℂ) else if k%2=r%2 then (z-(freeHillValue k : ℂ))⁻¹ else 0‖ ≤
      ‖Coeff.twoPoleReciprocalEnvelope n k‖ := by
  by_cases hk : k.natAbs=n
  · simp only [if_pos hk,norm_zero]
    exact norm_nonneg _
  rw [if_neg hk]
  by_cases hpar : k%2=r%2
  · rw [if_pos hpar,Coeff.twoPoleReciprocalEnvelope_apply,norm_mul,norm_inv,norm_inv,
      norm_inv,Complex.norm_intCast,Complex.norm_intCast]
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hpos : 0 < |(n : ℝ)^2-(k : ℝ)^2| :=
      lt_of_lt_of_le (by linarith) (two_mul_nat_sub_one_le_abs_sq_sub_sq hn hk)
    calc
      _ ≤ |(n : ℝ)^2-(k : ℝ)^2|⁻¹ :=
        inv_anti₀ hpos (freeHill_denominator_lower hn hz hk)
      _ = _ := by
        have he : |(n : ℝ)^2-(k : ℝ)^2| = |(k : ℝ)-(n : ℝ)| *|(k : ℝ)+(n : ℝ)| := by
          rw [← abs_mul,show (n : ℝ)^2-(k : ℝ)^2 = -(((k : ℝ)-(n : ℝ))*((k : ℝ)+(n : ℝ))) by ring,abs_neg]
        rw [he,mul_inv]
        simp only [Int.cast_sub,Int.cast_add,Int.cast_natCast]
  · simp only [if_neg hpar,norm_zero]
    exact norm_nonneg _

/-- The free boundary-source complement, as a total sequence family. Both
resonant entries are removed before applying the reciprocal symbol. -/
def hillFreeBoundaryGreen (n : ℕ) (r : ℤ) (z : ℂ) : Coeff 1 :=
  Coeff.ofFunctionOrZero 1 (fun k : ℤ =>
    if k.natAbs=n then 0 else if k%2=r%2 then (z-(freeHillValue k : ℂ))⁻¹ else 0)

theorem hillFreeBoundaryGreen_apply (n : ℕ) (hn : 1 ≤ n) (r : ℤ)
    (z : ℂ) (hz : z ∈ reducedHillStrip n) (k : ℤ) :
    hillFreeBoundaryGreen n r z k =
      if k.natAbs=n then 0 else if k%2=r%2 then (z-(freeHillValue k : ℂ))⁻¹ else 0 :=
  Coeff.ofFunctionOrZero_apply_of_mem 1 _
    ((lp.memℓp (Coeff.twoPoleReciprocalEnvelope n)).mono'
      (hillFreeBoundaryGreen_symbol_bound n hn r z hz)) k

/-- A uniform summable bound for the boundary-source inverse. -/
theorem norm_hillFreeBoundaryGreen_le (n : ℕ) (hn : 1 ≤ n) (r : ℤ)
    (z : ℂ) (hz : z ∈ reducedHillStrip n) : ‖hillFreeBoundaryGreen n r z‖ ≤ 4 := by
  apply (lp.norm_mono (by norm_num : (1 : ℝ≥0∞) ≠ 0) ?_).trans
    (Coeff.norm_twoPoleReciprocalEnvelope_le n)
  intro k
  rw [hillFreeBoundaryGreen_apply n hn r z hz]
  exact hillFreeBoundaryGreen_symbol_bound n hn r z hz k

/-- This vector inverts the constant source only on the actual complement. -/
theorem hillFreeBoundaryGreen_equation (n : ℕ) (hn : 1 ≤ n) (r : ℤ)
    (z : ℂ) (hz : z ∈ reducedHillStrip n) (k : ℤ) :
    (z-(freeHillValue k : ℂ))*hillFreeBoundaryGreen n r z k =
      if k.natAbs=n then 0 else if k%2=r%2 then 1 else 0 := by
  rw [hillFreeBoundaryGreen_apply n hn r z hz]
  by_cases hk : k.natAbs=n
  · simp only [if_pos hk,mul_zero]
  · rw [if_neg hk]
    split_ifs
    · exact mul_inv_cancel₀ (freeHill_denominator_ne_zero hn hz hk)
    · exact mul_zero _

/-- Analyticity is in the actual l1 norm on the common free energy strip. -/
theorem analyticOnNhd_hillFreeBoundaryGreen (n : ℕ) (hn : 1 ≤ n) (r : ℤ) :
    AnalyticOnNhd ℂ (hillFreeBoundaryGreen n r) (openHillStrip n) := by
  apply Coeff.analyticOnNhd_of_bounded_coordinatewise _ (isOpen_openHillStrip n) _ 4
    (fun z hz => norm_hillFreeBoundaryGreen_le n hn r z (openHillStrip_subset n hz))
  intro k z hz
  have hs : AnalyticAt ℂ (fun y : ℂ => if k.natAbs=n then (0 : ℂ)
      else if k%2=r%2 then (y-(freeHillValue k : ℂ))⁻¹ else 0) z := by
    by_cases hk : k.natAbs=n
    · simp only [if_pos hk]
      exact analyticAt_const
    · simp only [if_neg hk]
      by_cases hpar : k%2=r%2
      · simp only [if_pos hpar]
        exact (analyticAt_id.sub analyticAt_const).inv
          (freeHill_denominator_ne_zero hn (openHillStrip_subset n hz) hk)
      · simp only [if_neg hpar]
        exact analyticAt_const
  apply hs.congr
  filter_upwards [(isOpen_openHillStrip n).mem_nhds hz] with y hy
  exact (hillFreeBoundaryGreen_apply n hn r y (openHillStrip_subset n hy) k).symm

end NLS.KdV
