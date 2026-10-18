import NLS.ZakharovShabat.NLSRiccatiResidualBounds

/-! # Integral bounds for Riccati residual coefficients

Lower densities need pointwise bounds; their top derivative needs only an integral bound.
-/

noncomputable section
open Set Complex MeasureTheory
open scoped ContDiff
namespace NLS.ZakharovShabat

/-- Uniform pointwise bounds for lower densities and L1 bounds for their
derivatives control each residual coefficient, without top-derivative suprema. -/
theorem integral_norm_nlsRiccatiResidualPolynomial_coeff_le
    (a b : ℝ → ℂ) (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (N k : ℕ)
    (A B U D : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hU : 0 ≤ U) (hD : 0 ≤ D)
    (haB : ∀ x : ℝ, ‖a x‖ ≤ A) (hbB : ∀ x : ℝ, ‖b x‖ ≤ B)
    (hρ : ∀ j < N, ∀ x : ℝ, ‖nlsRiccatiDensity a b j x‖ ≤ U)
    (hρd : ∀ j < N, (∫ x in (0:ℝ)..1, ‖deriv (nlsRiccatiDensity a b j) x‖) ≤ D) :
    (∫ x in (0:ℝ)..1, ‖(nlsRiccatiResidualPolynomial a b N).coeff k x‖) ≤
      U+B+D+A*(k+1)*U^2 := by
  let P := nlsRiccatiTruncation a b N
  let P' := nlsRiccatiDerivativeTruncation a b N
  let Q := (Polynomial.C a*(P*P))*Polynomial.X^2
  have hP (j : ℕ) (x : ℝ) : ‖P.coeff j x‖ ≤ U := by
    dsimp only [P]
    rw [coeff_nlsRiccatiTruncation]
    split_ifs with hj
    · exact hρ j hj x
    · simpa using hU
  have hCb (x : ℝ) : ‖(Polynomial.C b).coeff k x‖ ≤ B := by
    rw [Polynomial.coeff_C]
    split_ifs
    · exact hbB x
    · simpa using hB
  have hprod (j : ℕ) (x : ℝ) : ‖(P*P).coeff j x‖ ≤ (j+1)*U^2 := by
    rw [Polynomial.coeff_mul]
    simp only [Finset.sum_apply,Pi.mul_apply]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ ij ∈ Finset.antidiagonal j, U^2 := by
        apply Finset.sum_le_sum
        intro ij _
        rw [norm_mul,pow_two]
        exact mul_le_mul (hP ij.1 x) (hP ij.2 x) (norm_nonneg _) hU
      _ = _ := by simp
  have hQ (x : ℝ) : ‖Q.coeff k x‖ ≤ A*(k+1)*U^2 := by
    dsimp only [Q]
    rw [Polynomial.coeff_mul_X_pow']
    split_ifs with hk
    · rw [Polynomial.coeff_C_mul]
      change ‖a x*((P*P).coeff (k-2) x)‖ ≤ _
      rw [norm_mul]
      have h := mul_le_mul (haB x) (hprod (k-2) x) (norm_nonneg _) hA
      apply h.trans
      have hkR : ((k-2:ℕ):ℝ)+1 ≤ (k:ℝ)+1 := by exact_mod_cast (show k-2+1 ≤ k+1 by omega)
      nlinarith [mul_nonneg hA (sq_nonneg U)]
    · simp only [Pi.zero_apply,norm_zero]
      positivity
  have hP' (j : ℕ) : Continuous (P'.coeff j) := by
    dsimp only [P']
    rw [coeff_nlsRiccatiDerivativeTruncation]
    split_ifs
    · exact (contDiff_infty_iff_deriv.mp (contDiff_nlsRiccatiDensity a b ha hb j)).2.continuous
    · exact continuous_const
  have hPX : Continuous ((P'*Polynomial.X).coeff k) := by
    cases k with
    | zero => rw [Polynomial.coeff_mul_X_zero]; exact continuous_zero
    | succ j => simpa only [Polynomial.coeff_mul_X] using hP' j
  have hDX : (∫ x in (0:ℝ)..1, ‖(P'*Polynomial.X).coeff k x‖) ≤ D := by
    cases k with
    | zero => simpa using hD
    | succ j =>
      rw [Polynomial.coeff_mul_X]
      dsimp only [P']
      rw [coeff_nlsRiccatiDerivativeTruncation]
      split_ifs with hj
      · exact hρd j hj
      · simpa using hD
  have hpoint (x : ℝ) : ‖(nlsRiccatiResidualPolynomial a b N).coeff k x‖ ≤
      U+B+‖(P'*Polynomial.X).coeff k x‖+A*(k+1)*U^2 := by
    change ‖((P+Polynomial.C b-P'*Polynomial.X-Q).coeff k) x‖ ≤ _
    simp only [Polynomial.coeff_sub,Polynomial.coeff_add,Pi.sub_apply,Pi.add_apply]
    exact (norm_sub_le _ _).trans (add_le_add
      ((norm_sub_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add (hP k x) (hCb x))) le_rfl)) (hQ x))
  have hright : Continuous (fun x => U+B+‖(P'*Polynomial.X).coeff k x‖+A*(k+1)*U^2) := by
    fun_prop
  have hi := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0:ℝ) ≤ 1)
    ((continuous_coeff_nlsRiccatiResidualPolynomial a b ha hb N k).norm.intervalIntegrable 0 1)
    (hright.intervalIntegrable 0 1) (fun x _ => hpoint x)
  have he : (∫ x in (0:ℝ)..1, U+B+‖(P'*Polynomial.X).coeff k x‖+A*(k+1)*U^2) =
      U+B+(∫ x in (0:ℝ)..1, ‖(P'*Polynomial.X).coeff k x‖)+A*(k+1)*U^2 := by
    have h1 : IntervalIntegrable (fun x : ℝ => U+B+‖(P'*Polynomial.X).coeff k x‖) volume 0 1 :=
      (continuous_const.add hPX.norm).intervalIntegrable 0 1
    have h2 : IntervalIntegrable (fun _ : ℝ => A*(k+1)*U^2) volume 0 1 :=
      continuous_const.intervalIntegrable 0 1
    have h3 : IntervalIntegrable (fun _ : ℝ => U+B) volume 0 1 :=
      continuous_const.intervalIntegrable 0 1
    have h4 : IntervalIntegrable (fun x : ℝ => ‖(P'*Polynomial.X).coeff k x‖) volume 0 1 :=
      hPX.norm.intervalIntegrable 0 1
    rw [intervalIntegral.integral_add h1 h2,intervalIntegral.integral_add h3 h4]
    simp
  rw [he] at hi
  exact hi.trans (by linarith)

end NLS.ZakharovShabat
