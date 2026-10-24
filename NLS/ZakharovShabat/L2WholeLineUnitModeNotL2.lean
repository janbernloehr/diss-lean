import NLS.ZakharovShabat.L2WholeLineFloquetMass
import NLS.ZakharovShabat.L2WholeLineOfPair
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Nonzero unit-multiplier physical modes are not globally square integrable -/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Matrix
namespace NLS.ZakharovShabat

/-- Positive periodic mass rules out a global L2 unit-multiplier mode,
including periodic and antiperiodic endpoint modes. -/
theorem not_memLp_l2WholeLineSolution_of_unit_floquet (u : IntervalPairL2) (z μ : ℂ)
    (hμ : ‖μ‖ = 1) (v : Fin 2 → ℂ) (hv0 : v ≠ 0)
    (hv : l2Monodromy u z *ᵥ v = μ • v) :
    ¬ MemLp (l2WholeLineSolution u z v) 2 volume := by
  intro hF
  have hi : Integrable (wholeLineSolutionMass u z v) :=
    (memLp_wholeLineVector_of_pair _ hF).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  let m := ∫ t in (0 : ℝ)..1, wholeLineSolutionMass u z v t
  have hm : 0 < m := wholeLineSolution_unit_mass_pos u z v hv0
  obtain ⟨n,hn⟩ := exists_nat_gt ((∫ t : ℝ, wholeLineSolutionMass u z v t)/m)
  have hbound : (n : ℝ)*m ≤ ∫ t : ℝ, wholeLineSolutionMass u z v t := by
    rw [← wholeLineSolution_mass_nat_periods u z μ hμ v hv n]
    rw [intervalIntegral.integral_of_le (Nat.cast_nonneg n)]
    exact setIntegral_le_integral hi (Filter.Eventually.of_forall (fun t => sq_nonneg _))
  exact (not_lt_of_ge hbound) ((div_lt_iff₀ hm).mp hn)

end NLS.ZakharovShabat
