import NLS.SequenceSpaces.UniformReciprocalMajorant

/-! # Sequence bounds for sums of varying reciprocal rows

The coefficient row is allowed to depend on the output index. A single
weighted convolution majorant controls every row and hence the actual
summed sequence. Absolute convergence and a quantitative norm bound are
proved together.
-/
noncomputable section
open scoped ENNReal
namespace NLS.Coeff
variable {p r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ r)]

/-- Uniformly bounded lp rows multiplied by one lr weight and divided
by index distance give an actual lr sequence of row sums, with absolute convergence. -/
theorem exists_reciprocal_rowSum_coefficients
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hr : r ≠ ⊤) (hr1 : 1 < r)
    (g : Coeff r) (a : ℤ → Coeff p) (u : ℤ → ℤ → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (ha : ∀ n, ‖a n‖ ≤ M)
    (hu : ∀ n k, ‖u n k‖ ≤ if k = n then 0 else ‖g k‖*‖a n k‖/|((n-k:ℤ):ℝ)|) :
    (∀ n, Summable (fun k => ‖u n k‖)) ∧
      ∃ b : Coeff r, (∀ n, b n = ∑' k, u n k) ∧
        ‖b‖ ≤ M*(‖g‖*‖puncturedLattice (min r p.conjExponent)
          (lt_min hr1 ((ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top))‖) := by
  obtain ⟨D,hD,hrows⟩ := exists_uniform_reciprocal_majorant hp hp1 hr hr1 g
  have hs (n : ℤ) : Summable (fun k => ‖u n k‖) :=
    (hrows (a n) n).1.of_nonneg_of_le (fun _ => norm_nonneg _) (hu n)
  let B : Coeff r := (M:ℂ) • D
  have hbound (n : ℤ) : ‖∑' k, u n k‖ ≤ ‖B n‖ := by
    calc
      _ ≤ ∑' k, ‖u n k‖ := norm_tsum_le_tsum_norm (hs n)
      _ ≤ ∑' k, if k = n then 0 else ‖g k‖*‖a n k‖/|((n-k:ℤ):ℝ)| :=
        (hs n).tsum_le_tsum (hu n) (hrows (a n) n).1
      _ ≤ ‖a n‖*‖D n‖ := (hrows (a n) n).2
      _ ≤ M*‖D n‖ := mul_le_mul_of_nonneg_right (ha n) (norm_nonneg _)
      _ = ‖B n‖ := by simp only [B,lp.coeFn_smul,Pi.smul_apply,norm_smul,Complex.norm_real,Real.norm_of_nonneg hM]
  let b : Coeff r := ⟨fun n => ∑' k, u n k,(lp.memℓp B).mono' hbound⟩
  refine ⟨hs,b,fun _ => rfl,?_⟩
  apply (lp.norm_mono (zero_lt_one.trans hr1).ne' hbound).trans
  change ‖B‖ ≤ _
  rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg hM]
  exact mul_le_mul_of_nonneg_left hD hM

end NLS.Coeff
