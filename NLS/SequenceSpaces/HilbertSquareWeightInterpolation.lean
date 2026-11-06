import NLS.SequenceSpaces.Multiplier
import NLS.SequenceSpaces.ConjugateDuality

/-! Exact midpoint interpolation of a literal complex diagonal on ell2.
The diagonal may be unbounded. Membership and the squared norm bound are
proved together from the two actual endpoint sequences by Holder. -/
noncomputable section
set_option autoImplicit false
open scoped ENNReal
namespace NLS.Coeff

/-- A pointwise square-weight relation supplies an actual middle weighted
Hilbert sequence and its sharp squared norm bound, without a boundedness
assumption on the diagonal. -/
theorem exists_middle_weight_of_square_relation
    (w : ℤ → ℂ) (a b : Coeff 2) (h : ∀ j : ℤ, b j=w j^2*a j) :
    ∃ c : Coeff 2, (∀ j, c j=w j*a j) ∧ ‖c‖^2≤‖a‖*‖b‖ := by
  have hp := lp.tsum_mul_le_mul_norm
    (show (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal from Real.HolderConjugate.two_two) a b
  have he (j : ℤ) : ‖w j*a j‖^2=‖a j‖*‖b j‖ := by
    rw [h j]
    simp only [norm_mul,norm_pow]
    ring
  have hs : Summable (fun j : ℤ => ‖w j*a j‖^2) := hp.1.congr (fun j => (he j).symm)
  have hm : Memℓp (fun j : ℤ => w j*a j) 2 := by
    apply memℓp_gen
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using hs
  let c : Coeff 2 := ⟨fun j => w j*a j,hm⟩
  refine ⟨c,fun _ => rfl,?_⟩
  have hn : ‖c‖^2=∑' j : ℤ, ‖w j*a j‖^2 := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
      lp.norm_rpow_eq_tsum (by norm_num : 0<(2 : ℝ≥0∞).toReal) c
  rw [hn,tsum_congr he]
  exact hp.2

/-- The midpoint estimate applies to any independently constructed middle
sequence satisfying the SAME literal square-weight relation. -/
theorem norm_sq_middle_weight_le (w : ℤ → ℂ) (a b c : Coeff 2)
    (hb : ∀ j, b j=w j^2*a j) (hc : ∀ j, c j=w j*a j) :
    ‖c‖^2≤‖a‖*‖b‖ := by
  obtain ⟨d,hd,hbound⟩ := exists_middle_weight_of_square_relation w a b hb
  have he : c=d := by ext j;rw [hc j,hd j]
  rwa [he]

end NLS.Coeff
