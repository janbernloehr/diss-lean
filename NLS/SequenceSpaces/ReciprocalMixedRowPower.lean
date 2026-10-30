import NLS.SequenceSpaces.CompactPuncturedKernel

/-!
# Mixed row powers for reciprocal matrix bounds

A zero-diagonal matrix bounded by an lp output sequence times inverse
integer distance has summable mixed row powers. Each row is dominated by
a translated punctured reciprocal lattice; the lp norm identity gives
the literal inner q-power sum and outer p/q power.
-/

noncomputable section
open scoped ENNReal
namespace NLS.Coeff
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- A reciprocal matrix majorant gives the literal mixed row-power summability. -/
theorem summable_mixedRowPower_of_reciprocal_bound
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hq1 : 1 < q)
    (M : ℤ → ℤ → ℂ) (b : Coeff p)
    (hdiag : ∀ m, M m m = 0)
    (hoff : ∀ m k, k ≠ m → ‖M m k‖ ≤ ‖b m‖/|((k-m:ℤ):ℝ)|) :
    Summable (fun m : ℤ => (∑' k : ℤ, ‖M m k‖ ^ q.toReal) ^ (p.toReal/q.toReal)) := by
  let c := puncturedLattice q hq1
  let B : Coeff p := (‖c‖:ℂ) • b
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos
    (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hp
  have hq0 : 0 < q.toReal := ENNReal.toReal_pos (zero_lt_one.trans hq1).ne' hq
  have hrow (m : ℤ) : ∃ row : Coeff q, (∀ k, row k = M m k) ∧ ‖row‖ ≤ ‖B m‖ := by
    let w : Coeff q := (‖b m‖:ℂ) • shift m c
    have hw (k : ℤ) : ‖w k‖ =
        ‖b m‖*(if k = m then 0 else |((k-m:ℤ):ℝ)|⁻¹) := by
      simp only [w,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,norm_mul,
        Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg (b m))]
      exact congrArg (‖b m‖*·) (norm_shift_puncturedLattice_apply hq1 m k)
    have hdom (k : ℤ) : ‖M m k‖ ≤ ‖w k‖ := by
      rw [hw]
      by_cases hkm : k = m
      · subst k; simp [hdiag]
      · simpa only [if_neg hkm,div_eq_mul_inv] using hoff m k hkm
    let row : Coeff q := ⟨M m,(lp.memℓp w).mono' hdom⟩
    refine ⟨row,fun _ => rfl,(lp.norm_mono (zero_lt_one.trans hq1).ne' hdom).trans_eq ?_⟩
    simp only [w,B,norm_smul,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,norm_mul,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg (b m)),
      abs_of_nonneg (norm_nonneg c),norm_shift]
    ring
  choose row hroweq hrowbound using hrow
  have he (m : ℤ) : (∑' k : ℤ, ‖M m k‖ ^ q.toReal) ^ (p.toReal/q.toReal) =
      ‖row m‖ ^ p.toReal := by
    have ht : (∑' k : ℤ, ‖M m k‖ ^ q.toReal) = ‖row m‖ ^ q.toReal := by
      rw [lp.norm_rpow_eq_tsum hq0]
      simp only [hroweq]
    rw [ht,← Real.rpow_mul (norm_nonneg (row m))]
    congr 1
    field_simp
  simp only [he]
  exact ((lp.memℓp B).summable hp0).of_nonneg_of_le
    (fun _ => Real.rpow_nonneg (norm_nonneg _) _)
    (fun m => Real.rpow_le_rpow (norm_nonneg _) (hrowbound m) hp0.le)

end NLS.Coeff
