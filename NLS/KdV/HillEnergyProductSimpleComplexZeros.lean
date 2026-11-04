import NLS.KdV.HillEnergyProductComplexZeros
import NLS.KdV.HillProductDirectionalDerivative

/-! Distinct retained energies give SIMPLE zeros of the literal
complex Hill product. Moving one data coordinate fills its zero factor
and proves the actual derivative nonzero, without a formal product
logarithmic derivative or any reality assumption. -/
noncomputable section
open Set Complex
open scoped ENNReal Classical
namespace NLS.KdV

theorem hillEnergyProductCoordinateDerivative_ne_zero_of_injective (n m : ℕ+) (hmn : m ≠ n)
    (d : lp (fun _ : ℕ+ => ℂ) 2) (hinj : Function.Injective (fun k : ℕ+ => hillEnergySequenceZero k d)) :
    hillEnergyProductCoordinateDerivative n m (hillEnergySequenceZero m d,d) ≠ 0 := by
  have hshift : hillEnergySequenceProduct n (hillEnergySequenceZero m d,hillZeroCoordinateShift m d 1) ≠ 0 := by
    apply hillEnergySequenceProduct_ne_zero_of_off_roots
    intro k _
    by_cases hkm : k = m
    · subst k
      rw [hillEnergySequenceZero_shift_selected,mul_one]
      intro he
      have hm : ((m:ℕ):ℂ) = 0 := by linear_combination -he
      exact (by exact_mod_cast m.ne_zero : ((m:ℕ):ℂ) ≠ 0) hm
    · have hk : hillEnergySequenceZero k (hillZeroCoordinateShift m d 1) = hillEnergySequenceZero k d := by
        unfold hillEnergySequenceZero
        rw [hillZeroCoordinateShift_apply,if_neg hkm,add_zero]
      rw [hk]
      exact fun he => hkm (hinj he).symm
  rw [hillEnergyProductCoordinateDerivative,hillEnergySequenceProduct_retained_root n m hmn,sub_zero]
  exact hshift

theorem hillEnergySequenceProduct_energy_deriv_ne_zero_of_injective (n m : ℕ+) (hmn : m ≠ n)
    (d : lp (fun _ : ℕ+ => ℂ) 2) (hinj : Function.Injective (fun k : ℕ+ => hillEnergySequenceZero k d)) :
    deriv (fun E : ℂ => hillEnergySequenceProduct n (E,d)) (hillEnergySequenceZero m d) ≠ 0 := by
  have hD := hillEnergyProductCoordinateDerivative_ne_zero_of_injective n m hmn d hinj
  intro hz
  apply hD
  rw [hillEnergyProductCoordinateDerivative_at_retained_root n m hmn,hz,mul_zero]

end NLS.KdV
