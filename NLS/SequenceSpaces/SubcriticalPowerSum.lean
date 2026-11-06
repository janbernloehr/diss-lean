import NLS.SequenceSpaces.ReciprocalSeries
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Sharp finite power sums below the harmonic exponent, including the
integrable singular endpoint of the continuous comparison. -/
noncomputable section
open Set MeasureTheory
namespace NLS.ReciprocalSeries

theorem sum_range_succ_negative_power_le (s : ℝ) (hs : 0 ≤ s) (hs1 : s < 1) (n : ℕ) :
    (∑ j ∈ Finset.range n, ((j:ℝ)+1)^(-s)) ≤ (n:ℝ)^(1-s)/(1-s) := by
  have hi (j : ℕ) : IntervalIntegrable (fun x : ℝ => x^(-s)) volume (j:ℝ) (j+1:ℕ) :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hstep (j : ℕ) : ((j:ℝ)+1)^(-s) ≤
      ∫ x : ℝ in (j:ℝ)..(j+1:ℕ), x^(-s) := by
    calc
      _ = ∫ _x : ℝ in (j:ℝ)..(j+1:ℕ), ((j:ℝ)+1)^(-s) := by simp
      _ ≤ _ := intervalIntegral.integral_mono_on_of_le_Ioo (by norm_cast; omega)
        (by apply intervalIntegrable_const) (hi j) (fun x hx =>
          Real.rpow_le_rpow_of_nonpos (by linarith [hx.1,Nat.cast_nonneg (α:=ℝ) j])
            (by exact_mod_cast hx.2.le) (neg_nonpos.mpr hs))
  calc
    _ ≤ ∑ j ∈ Finset.range n, ∫ x : ℝ in (j:ℝ)..(j+1:ℕ), x^(-s) :=
      Finset.sum_le_sum (fun j _ => hstep j)
    _ = ∫ x : ℝ in (0:ℝ)..n, x^(-s) := by
      simpa only [Nat.cast_zero] using intervalIntegral.sum_integral_adjacent_intervals
        (a := fun j : ℕ => (j:ℝ)) (n := n) (fun j _ => hi j)
    _ = _ := by
      rw [integral_rpow (Or.inl (by linarith)),
        show -s+1=1-s by ring,Real.zero_rpow (by linarith : 1-s≠0),sub_zero]

end NLS.ReciprocalSeries
