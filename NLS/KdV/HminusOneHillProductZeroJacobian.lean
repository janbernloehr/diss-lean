import NLS.KdV.HillProductDirectionalDerivative
import NLS.KdV.HminusOneHillPsiProductContinuity
import NLS.KdV.HminusOneHillPsiZeroNoncollision

/-! At the ACTUAL original real Hill zero sequence, evaluating the
product's sequence derivative at its retained zeros gives a diagonal
matrix with nonzero diagonal. This includes every low/collapsed gap.
No Banach operator inverse or common complex zero domain is asserted. -/
noncomputable section
open Set Complex
open scoped ENNReal Classical
namespace NLS.KdV

theorem hillEnergySequenceZero_real (n m : ℕ+) (q : PeriodOneRealHminusOne) :
    hillEnergySequenceZero m (hillHminusPsiZeroDisplacement n q) =
      (hillHminusCanonicalPsiRealZero n m q.val q.property:ℂ) := by
  unfold hillEnergySequenceZero
  change ((Real.pi:ℂ)*(m:ℕ))^2+(m:ℕ)*
    (((hillHminusCanonicalPsiRealZero n m q.val q.property:ℂ)-((Real.pi:ℂ)*(m:ℕ))^2)/(m:ℕ)) = _
  have hm : ((m:ℕ):ℂ) ≠ 0 := by exact_mod_cast m.ne_zero
  field_simp
  ring

theorem hillEnergySequenceProduct_energy_deriv_ne_zero_at_real_root (n m : ℕ+) (hmn : m ≠ n)
    (q : PeriodOneRealHminusOne) :
    deriv (fun E : ℂ => hillEnergySequenceProduct n (E,hillHminusPsiZeroDisplacement n q))
      (hillEnergySequenceZero m (hillHminusPsiZeroDisplacement n q)) ≠ 0 := by
  rw [hillEnergySequenceZero_real]
  let E : ℂ := (hillHminusCanonicalPsiRealZero n m q.val q.property:ℂ)
  let d := hillHminusPsiZeroDisplacement n q
  let A := hillHminusPsiProductScalar n q.val q.property
  have hP := hillHminusCanonicalPsi_deriv_ne_zero_of_real_source q.val q.property n E
    (hillHminusCanonicalPsiRealZero_is_zero n m q.val q.property hmn)
  have he : (fun w : ℂ => hillHminusCanonicalPsi n (w,q.val)) =
      (fun w : ℂ => A*hillEnergySequenceProduct n (w,d)) :=
    funext (fun w => hillHminusCanonicalPsi_eq_scalar_mul_literalProduct n w q)
  have hd := ((analyticAt_hillEnergySequenceProduct n (E,d)).comp
    (f := fun w : ℂ => (w,d)) (analyticAt_id.prod analyticAt_const)).differentiableAt.hasDerivAt
  have hA := hd.const_mul A
  dsimp only [Function.comp_def] at hA
  rw [← he] at hA
  intro hz
  change deriv (fun w : ℂ => hillEnergySequenceProduct n (w,d)) E = 0 at hz
  rw [hz,mul_zero] at hA
  exact hP hA.deriv

theorem hillEnergyProductCoordinateDerivative_real_diagonal_ne_zero (n m : ℕ+) (hmn : m ≠ n)
    (q : PeriodOneRealHminusOne) :
    hillEnergyProductCoordinateDerivative n m
      (hillEnergySequenceZero m (hillHminusPsiZeroDisplacement n q),hillHminusPsiZeroDisplacement n q) ≠ 0 := by
  rw [hillEnergyProductCoordinateDerivative_at_retained_root n m hmn]
  exact mul_ne_zero (neg_ne_zero.mpr (by exact_mod_cast m.ne_zero))
    (hillEnergySequenceProduct_energy_deriv_ne_zero_at_real_root n m hmn q)

theorem hillEnergyProductCoordinateDerivative_real_off_diagonal (n m k : ℕ+)
    (hmn : m ≠ n) (hkn : k ≠ n) (hmk : m ≠ k) (q : PeriodOneRealHminusOne) :
    hillEnergyProductCoordinateDerivative n m
      (hillEnergySequenceZero k (hillHminusPsiZeroDisplacement n q),hillHminusPsiZeroDisplacement n q) = 0 := by
  let d := hillHminusPsiZeroDisplacement n q
  have hne : hillEnergySequenceZero m d ≠ hillEnergySequenceZero k d := by
    rw [hillEnergySequenceZero_real,hillEnergySequenceZero_real]
    exact fun h => hmk (hillHminusCanonicalPsiRealZero_injective n q.val q.property (Complex.ofReal_inj.mp h))
  have h := hillEnergyProductCoordinateDerivative_restore n m hmn (hillEnergySequenceZero k d) d
  rw [hillEnergySequenceProduct_retained_root n k hkn d,mul_zero] at h
  exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hne)

theorem hillHminusProduct_zero_evaluation_Jacobian (n k : ℕ+) (hkn : k ≠ n)
    (q : PeriodOneRealHminusOne) (m : ℕ+) :
    fderiv ℂ (hillEnergySequenceProduct n)
      (hillEnergySequenceZero k (hillHminusPsiZeroDisplacement n q),hillHminusPsiZeroDisplacement n q)
      (0,lp.single 2 m 1) ≠ 0 ↔ m = k := by
  rw [fderiv_hillEnergySequenceProduct_coordinate]
  by_cases hmk : m = k
  · subst m
    exact ⟨fun _ => rfl,fun _ => hillEnergyProductCoordinateDerivative_real_diagonal_ne_zero n k hkn q⟩
  · have hz : hillEnergyProductCoordinateDerivative n m
        (hillEnergySequenceZero k (hillHminusPsiZeroDisplacement n q),hillHminusPsiZeroDisplacement n q) = 0 := by
      by_cases hmn : m = n
      · subst m
        exact hillEnergyProductCoordinateDerivative_omitted n _
      · exact hillEnergyProductCoordinateDerivative_real_off_diagonal n m k hmn hkn hmk q
    simp only [hz,ne_eq,not_true_eq_false,hmk]

end NLS.KdV
