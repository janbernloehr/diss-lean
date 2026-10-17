import NLS.SequenceSpaces.Weighted

/-! # Raw single Fourier coefficients in weighted spaces

Single directions retain their prescribed raw amplitude. Their weighted norm
therefore includes the weight at the chosen signed frequency.
-/
noncomputable section
open scoped ENNReal
namespace NLS.WeightedCoeff
variable {p : ℝ≥0∞}

/-- The raw coefficient c at frequency n, and zero at every other frequency. -/
def single (w : Weight) (n : ℤ) (c : ℂ) : WeightedCoeff w p :=
  (weightEquiv w p).symm (lp.single p n ((w n:ℂ)*c))

@[simp] theorem single_val (w : Weight) (n : ℤ) (c : ℂ) (j : ℤ) :
    (single (p := p) w n c).val j = (Pi.single n c : ℤ → ℂ) j := by
  change ((lp.single p n ((w n:ℂ)*c) : Coeff p) j)/(w j:ℂ) = _
  by_cases h : j = n
  · subst j
    simp [lp.single_apply,w.complex_ne_zero]
  · simp [lp.single_apply,h]

@[simp] theorem weightEquiv_single (w : Weight) (n : ℤ) (c : ℂ) :
    weightEquiv w p (single w n c) = lp.single p n ((w n:ℂ)*c) :=
  (weightEquiv w p).apply_symm_apply _

/-- A raw unit direction has norm equal to its weight, without rescaling its coefficient. -/
theorem norm_single [Fact (1 ≤ p)] (w : Weight) (n : ℤ) (c : ℂ) :
    ‖single (p := p) w n c‖ = w n * ‖c‖ := by
  rw [norm_eq,weightEquiv_single,lp.norm_single (zero_lt_one.trans_le (Fact.out : 1 ≤ p)),
    norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (w.positive n)]

end NLS.WeightedCoeff
