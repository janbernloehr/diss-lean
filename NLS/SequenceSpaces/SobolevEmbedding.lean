import NLS.SequenceSpaces.Embedding
import Mathlib.Analysis.PSeries

/-!
# The one-derivative Fourier–Lebesgue embedding

This is the coefficient-space version of Appendix A, Lemma A.8 in the
dissertation: `FL^{1,p} → FL^1`, for `1 ≤ p < ∞`. We retain the explicit Hölder
constant instead of asserting that the embedding has norm one.
-/

open scoped ENNReal
noncomputable section

namespace NLS

/-- Summability of inverse powers of `1 + |n|` on integer frequencies. -/
theorem summable_inverse_bracket {r : ℝ} (hr : 1 < r) :
    Summable (fun n : ℤ => 1 / (1 + |(n : ℝ)|) ^ r) := by
  have h := (Real.summable_one_div_nat_add_rpow 1 r).mpr hr
  have hNat : Summable (fun n : ℕ => 1 / (1 + (n : ℝ)) ^ r) := by
    convert h using 1
    funext n
    rw [abs_of_nonneg (by positivity), add_comm]
  apply Summable.of_nat_of_neg
  · simpa only [Int.cast_natCast, Nat.abs_cast] using hNat
  · simpa only [Int.cast_neg, abs_neg, Int.cast_natCast, Nat.abs_cast] using hNat

namespace Weight

/-- The inverse one-derivative weight belongs to every `lq` with `q > 1`. -/
theorem inverse_sobolev_one_memlp {q : ℝ≥0∞} (hq : 1 < q) :
    Memℓp (fun n => (sobolev 1 n : ℂ)⁻¹) q := by
  have hnorm (n : ℤ) : ‖(sobolev 1 n : ℂ)⁻¹‖ = (1 + |(n : ℝ)|)⁻¹ := by
    simp only [sobolev_apply, Real.rpow_one, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 + |(n : ℝ)|)]
  by_cases htop : q = ⊤
  · subst q
    apply memℓp_infty
    refine ⟨1, ?_⟩
    rintro _ ⟨n, rfl⟩
    change ‖(sobolev 1 n : ℂ)⁻¹‖ ≤ 1
    rw [hnorm n]
    exact inv_le_one_of_one_le₀ (by linarith [abs_nonneg (n : ℝ)])
  · have hqr : 1 < q.toReal := by
      have := (ENNReal.toReal_lt_toReal ENNReal.one_ne_top htop).mpr hq
      simpa only [ENNReal.toReal_one] using this
    rw [memℓp_gen_iff (zero_lt_one.trans hqr)]
    apply (summable_inverse_bracket hqr).congr
    intro n
    change 1 / (1 + |(n : ℝ)|) ^ q.toReal = ‖(sobolev 1 n : ℂ)⁻¹‖ ^ q.toReal
    rw [hnorm n, Real.inv_rpow (by positivity), one_div]

end Weight

namespace WeightedCoeff

variable (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- The explicit norm of the inverse Sobolev weight in the conjugate space. -/
def sobolevEmbeddingConstant (hp : p ≠ ⊤) : ℝ :=
  ‖inverseWeight (q := p.conjExponent) (Weight.sobolev 1)
    (Weight.inverse_sobolev_one_memlp
      ((ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top))‖

theorem sobolevEmbeddingConstant_nonneg (hp : p ≠ ⊤) :
    0 ≤ sobolevEmbeddingConstant p hp := by
  unfold sobolevEmbeddingConstant
  exact lp.norm_nonneg' _

/-- The continuous embedding from one-derivative coefficients into `l1`. -/
def sobolevToL1CLM (hp : p ≠ ⊤) : WeightedCoeff (Weight.sobolev 1) p →L[ℂ] Coeff 1 := by
  letI : Fact (1 ≤ p.conjExponent) :=
    ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩
  exact toL1CLM (q := p.conjExponent) (Weight.sobolev 1)
    (Weight.inverse_sobolev_one_memlp
      ((ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top))

@[simp]
theorem sobolevToL1CLM_apply (hp : p ≠ ⊤)
    (a : WeightedCoeff (Weight.sobolev 1) p) (n : ℤ) :
    sobolevToL1CLM p hp a n = a.val n := by
  simp only [sobolevToL1CLM, toL1CLM_apply]

/-- The embedding estimate, with a constant depending only on `p`. -/
theorem norm_sobolevToL1CLM_le (hp : p ≠ ⊤)
    (a : WeightedCoeff (Weight.sobolev 1) p) :
    ‖sobolevToL1CLM p hp a‖ ≤ sobolevEmbeddingConstant p hp * ‖a‖ := by
  let : Fact (1 ≤ p.conjExponent) :=
    ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩
  exact norm_toL1CLM_le _ _ a

end WeightedCoeff
end NLS
