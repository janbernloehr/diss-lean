import NLS.ZakharovShabat.AppendixDReciprocalBounds

/-! # Explicit separation power in the square-row estimate of D.6 -/
noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The squared-row majorant has p/2 energy with separation constant c^p. -/
theorem exists_appendixDSquaredRow_power_bound (hp1 : 1 < p) (hp : p ≠ ⊤)
    (r : Coeff ⊤) (a : Coeff p) {c : ℝ} {N : ℕ}
    (hc : 0 < c) (hsep : AppendixDReferenceSeparated r c N) :
    ∃ Q : Coeff (p/2),
      (∀ n : ℤ, N ≤ n.natAbs → ∀ z ∈ refinedResonantDisk n,
        (∑' m, ‖appendixDReciprocalTerm r a n z m‖^2) ≤ c^2*‖Q n‖) ∧
      Summable (fun n : ℤ => (c^2*‖Q n‖)^((p/2).toReal)) ∧
      (∑' n : ℤ, (c^2*‖Q n‖)^((p/2).toReal)) ≤
        c^p.toReal*‖a‖^p.toReal*
          (NLS.Fourier.squaredAbsoluteRowConstant hp1 hp)^((p/2).toReal) := by
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos (zero_lt_one.trans hp1).ne' hp
  have hq : 0 < (p/2).toReal := by
    simp only [ENNReal.toReal_div,ENNReal.toReal_ofNat]
    positivity
  have hC : 0 ≤ NLS.Fourier.squaredAbsoluteRowConstant hp1 hp := lp.norm_nonneg' _
  obtain ⟨Q,hQ,hQn⟩ := exists_appendixDSquaredRowSup hp1 hp r a hc hsep
  let B : Coeff (p/2) := ((c^2:ℝ):ℂ) • Q
  have he (n : ℤ) : ‖B n‖ = c^2*‖Q n‖ := by
    simp only [B,lp.coeFn_smul,Pi.smul_apply,norm_smul,Complex.norm_real,
      Real.norm_of_nonneg (sq_nonneg c)]
  have hB : ‖B‖ ≤ c^2*(‖a‖^2*NLS.Fourier.squaredAbsoluteRowConstant hp1 hp) := by
    change ‖((c^2:ℝ):ℂ) • Q‖ ≤ _
    rw [lp.norm_const_smul (ENNReal.toReal_pos_iff.mp hq).1.ne',Complex.norm_real,
      Real.norm_of_nonneg (sq_nonneg c)]
    exact mul_le_mul_of_nonneg_left hQn (sq_nonneg c)
  have hs : Summable (fun n : ℤ => (c^2*‖Q n‖)^((p/2).toReal)) := by
    simpa only [he] using B.property.summable hq
  have hpow (x : ℝ) (hx : 0 ≤ x) : (x^2)^((p/2).toReal) = x^p.toReal := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hx]
    congr 1
    simp only [ENNReal.toReal_div,ENNReal.toReal_ofNat]
    ring
  refine ⟨Q,hQ,hs,?_⟩
  calc
    _ = ‖B‖^((p/2).toReal) := by
      rw [lp.norm_rpow_eq_tsum hq]
      simp only [he]
    _ ≤ (c^2*(‖a‖^2*NLS.Fourier.squaredAbsoluteRowConstant hp1 hp))^((p/2).toReal) :=
      Real.rpow_le_rpow (lp.norm_nonneg' B) hB hq.le
    _ = _ := by
      rw [Real.mul_rpow (sq_nonneg c) (mul_nonneg (sq_nonneg ‖a‖) hC),
        Real.mul_rpow (sq_nonneg ‖a‖) hC,hpow c hc.le,hpow ‖a‖ (norm_nonneg _)]
      ring

end NLS.ZakharovShabat
