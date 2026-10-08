import NLS.SequenceSpaces.SquaredReciprocalRows
import NLS.SequenceSpaces.QuasiHolderProduct
import NLS.SequenceSpaces.QuasiExponentEmbedding
import NLS.Fourier.HilbertKernel

/-! # Squared absolute reciprocal rows at the half exponent

Powered Young gives an ell-(p/2) majorant for squared reciprocal rows,
also for 1 < p < 2. No Banach assumption is made on the target exponent.
-/
noncomputable section
open scoped ENNReal
namespace NLS.Fourier
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The reciprocal-square convolution constant for the half exponent. -/
def squaredAbsoluteRowConstant (hp1 : 1 < p) (hp : p ≠ ⊤) : ℝ :=
  ‖squaredReciprocalKernel (min 1 (p.toReal/2))
    (lt_min (by norm_num) (by
      have h := (ENNReal.toReal_lt_toReal (by simp) hp).mpr hp1
      norm_num at h
      linarith))‖

/-- The square of a coefficient sequence, including quasi-normed targets. -/
def halfSquareCoeff (a : Coeff p) : Coeff (p/2) := by
  let : p.HolderTriple p (p/2) := Coeff.holderTriple_half p
  exact Coeff.quasiHolderProduct a a

omit [Fact (1 ≤ p)] in
@[simp] theorem halfSquareCoeff_apply (a : Coeff p) (n : ℤ) :
    halfSquareCoeff a n = a n^2 := by change a n*a n = _; ring

/-- Squaring has its expected quadratic norm bound even below exponent one. -/
theorem norm_halfSquareCoeff_le (hp : p ≠ ⊤) (a : Coeff p) :
    ‖halfSquareCoeff a‖ ≤ ‖a‖^2 := by
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos
    (ne_of_gt (zero_lt_one.trans_le (Fact.out : 1 ≤ p))) hp
  let : p.HolderTriple p (p/2) := Coeff.holderTriple_half p
  unfold halfSquareCoeff
  simpa only [pow_two] using Coeff.norm_quasiHolderProduct_le (r := p/2) hp0 hp0 a a

/-- One half-exponent sequence is exactly the absolute square row at every index. -/
theorem exists_squaredAbsoluteRows (hp1 : 1 < p) (hp : p ≠ ⊤) (a : Coeff p) :
    ∃ b : Coeff (p/2),
      (∀ n : ℤ,
        Summable (fun m : ℤ => ‖a m‖^2*‖hilbertKernel (n-m)‖^2) ∧
        b n = ((∑' m : ℤ, ‖a m‖^2*‖hilbertKernel (n-m)‖^2 : ℝ):ℂ)) ∧
      ‖b‖ ≤ ‖a‖^2*squaredAbsoluteRowConstant hp1 hp := by
  have hpr : 1 < p.toReal := by
    simpa using (ENNReal.toReal_lt_toReal (by simp) hp).mpr hp1
  have hr : (1/2:ℝ) < p.toReal/2 := by linarith
  have he := Coeff.halfExponent_eq_div hp
  let a2 : Coeff (ENNReal.ofReal (p.toReal/2)) :=
    ⟨⇑(halfSquareCoeff a),by
      change Memℓp (⇑(halfSquareCoeff a)) _
      rw [he]
      exact lp.memℓp (halfSquareCoeff a)⟩
  have ha2 : ‖a2‖ ≤ ‖a‖^2 := by
    have hr0 : 0 < p.toReal/2 := by linarith
    have hhalf : 0 < (p/2).toReal := by simpa using hr0
    have heNorm : ‖a2‖ = ‖halfSquareCoeff a‖ := by
      rw [lp.norm_eq_tsum_rpow (by simpa only [ENNReal.toReal_ofReal hr0.le] using hr0),
        lp.norm_eq_tsum_rpow hhalf]
      simp only [ENNReal.toReal_ofReal hr0.le,ENNReal.toReal_div,ENNReal.toReal_ofNat]
      rfl
    rw [heNorm]
    exact norm_halfSquareCoeff_le hp a
  let K := squaredReciprocalKernel (min 1 (p.toReal/2)) (lt_min (by norm_num) hr)
  obtain ⟨b,hb,hbn⟩ := exists_squaredReciprocalRow (p.toReal/2) hr a2
  have hterm (n k : ℤ) : ‖a2 (n-k)*K k‖ = ‖a (n-k)‖^2*‖hilbertKernel k‖^2 := by
    rw [norm_mul]
    change ‖halfSquareCoeff a (n-k)‖*‖K k‖ = _
    rw [halfSquareCoeff_apply,norm_pow]
    congr 1
    by_cases hk : k = 0
    · simp [K,hk,hilbertKernel]
    · simp only [K,squaredReciprocalKernel_apply,if_neg hk,Complex.norm_real,
        Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (|(k:ℝ)|)),
        Real.rpow_neg (abs_nonneg _),Real.rpow_two,hilbertKernel,
        norm_neg,norm_inv,Complex.norm_intCast,inv_pow]
  have hrows (n : ℤ) :
      Summable (fun m : ℤ => ‖a m‖^2*‖hilbertKernel (n-m)‖^2) ∧
      b n = ((∑' m : ℤ, ‖a m‖^2*‖hilbertKernel (n-m)‖^2 : ℝ):ℂ) := by
    have hsum := ((hb n).1.congr (fun k => hterm n k)).comp_injective (Equiv.subLeft n).injective
    constructor
    · simpa only [Function.comp_def,Equiv.subLeft_apply,sub_sub_cancel] using hsum
    · rw [(hb n).2]
      congr 1
      rw [← (Equiv.subLeft n).tsum_eq (fun m : ℤ => ‖a m‖^2*‖hilbertKernel (n-m)‖^2)]
      apply tsum_congr
      intro k
      simpa only [Equiv.subLeft_apply,sub_sub_cancel] using hterm n k
  have hnorm : ‖b‖ ≤ ‖a‖^2*squaredAbsoluteRowConstant hp1 hp :=
    hbn.trans (mul_le_mul_of_nonneg_right ha2 (by apply lp.norm_nonneg'))
  rw [← he]
  exact (show ∃ b : Coeff (ENNReal.ofReal (p.toReal/2)),
    (∀ n : ℤ, Summable (fun m : ℤ => ‖a m‖^2*‖hilbertKernel (n-m)‖^2) ∧
      b n = ((∑' m : ℤ, ‖a m‖^2*‖hilbertKernel (n-m)‖^2 : ℝ):ℂ)) ∧
      ‖b‖ ≤ ‖a‖^2*squaredAbsoluteRowConstant hp1 hp from ⟨b,hrows,hnorm⟩)

end NLS.Fourier
