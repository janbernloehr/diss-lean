import NLS.MKdV.MiuraL2MassActionFrequency
import NLS.ZakharovShabat.SourceMomentumFrequencyL2Extension

/-! # The full original real L² mass/momentum frequency comparison

The independent Hill K_1 action derivative and the original NLS S_2
frequency have the same positive period-one value. The NLS frequency
is independently identified as the unique continuous extension of its
actual angle-momentum bracket. The printed parity factor fails already
at m=1, including at the literal zero profile.
-/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem miura_mass_frequency_eq_NLS_momentum (D : MiuraL2MassActionData) (a : Coeff 2)
    (ha : ∀ j, a j = conj (a (-j))) (n : ℤ) (hn : 0 < n) :
    D.frequency n (miuraL2ActionMeanMap a) = sourceMomentumFrequency n (scalarL2Diagonal a) :=
  D.frequency_eq a ha n hn

theorem miura_mass_frequency_printed_parity_ne (D : MiuraL2MassActionData) (a : Coeff 2)
    (ha : ∀ j, a j = conj (a (-j))) (n : ℤ) (hn : 0 < n) :
    (-1 : ℂ)^1*sourceMomentumFrequency n (scalarL2Diagonal a) ≠ D.frequency n (miuraL2ActionMeanMap a) := by
  intro he
  rw [D.frequency_eq a ha n hn,sourceMomentumFrequency] at he
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  have hc : (2*(Real.pi : ℂ)*n) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) hn0
  apply hc
  norm_num only [pow_one,neg_one_mul] at he
  linear_combination -(1/2 : ℂ)*he

/-- A concrete zero-profile counterexample to the source's printed
(-1)^m frequency factor. Both selected actions are closed here, where
the source explicitly asserts analytic frequency continuation. -/
theorem miura_mass_frequency_printed_parity_zero_counterexample :
    (-1 : ℂ)^1*sourceMomentumFrequency 1 (scalarL2Diagonal 0) ≠
      miuraL2MassActionData.frequency 1 (miuraL2ActionMeanMap 0) := by
  apply miura_mass_frequency_printed_parity_ne miuraL2MassActionData 0
  · intro j
    simp
  · norm_num

end NLS.MKdV
