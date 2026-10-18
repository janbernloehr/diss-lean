import NLS.Fourier.BoundedLatticeMomentSeries

/-! # Removable divided differences of Fourier samples

The moment series for the spectral divided difference converges in L2 with an exponential norm bound, including zero displacements.
-/

noncomputable section
open Set Complex MeasureTheory
open scoped ENNReal
namespace NLS.Fourier

private theorem norm_latticeDifference_symbol_le (δ : NLS.Coeff ⊤) (k : ℕ) (n : ℤ) :
    ‖(-2*I)^(k+1)*(δ n)^k/((k+1).factorial:ℂ)‖ ≤ 2*((2*‖δ‖)^k/(k.factorial:ℝ)) := by
  simp only [norm_div,norm_mul,norm_pow,norm_neg,norm_ofNat,norm_I,mul_one,Complex.norm_natCast]
  calc
    _ ≤ 2^(k+1)*‖δ‖^k/(k.factorial:ℝ) := by
      gcongr
      · exact lp.norm_apply_le_norm (by simp) δ n
      · omega
    _ = _ := by rw [pow_succ,mul_pow]; ring

/-- The kth moment of the removable divided difference in spectral
displacement, defined even when a displacement coordinate is zero. -/
def boundedLatticeDifferenceTerm (f : ℝ → ℂ) (hf : Continuous f)
    (δ : NLS.Coeff ⊤) (k : ℕ) : NLS.Coeff 2 :=
  ⟨fun n => ((-2*I)^(k+1)*(δ n)^k/((k+1).factorial:ℂ))*unitIntervalMomentCoefficients f hf (k+1) n, by
    apply ((lp.memℓp (unitIntervalMomentCoefficients f hf (k+1))).norm.const_mul
      (2*((2*‖δ‖)^k/(k.factorial:ℝ)))).mono
    intro n
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (norm_latticeDifference_symbol_le δ k n) (norm_nonneg _)⟩

@[simp] theorem boundedLatticeDifferenceTerm_apply (f : ℝ → ℂ) (hf : Continuous f)
    (δ : NLS.Coeff ⊤) (k : ℕ) (n : ℤ) :
    boundedLatticeDifferenceTerm f hf δ k n =
      ((-2*I)^(k+1)*(δ n)^k/((k+1).factorial:ℂ))*periodOneCoefficient (fun x => (x:ℂ)^(k+1)*f x) n := by
  simp only [boundedLatticeDifferenceTerm,unitIntervalMomentCoefficients_apply]

/-- The divided-difference moments have a factorial bound with factor two. -/
theorem norm_boundedLatticeDifferenceTerm_le (f : ℝ → ℂ) (hf : Continuous f)
    (δ : NLS.Coeff ⊤) (k : ℕ) :
    ‖boundedLatticeDifferenceTerm f hf δ k‖ ≤ (2*((2*‖δ‖)^k/(k.factorial:ℝ)))*
      ‖unitIntervalMemLpCoefficients f (memLp_two_interval hf 0 1 (by norm_num))‖ := by
  let B : ℝ := 2*((2*‖δ‖)^k/(k.factorial:ℝ))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hnorm : ‖boundedLatticeDifferenceTerm f hf δ k‖ ≤
      ‖(B:ℂ) • unitIntervalMomentCoefficients f hf (k+1)‖ := by
    apply lp.norm_mono (by norm_num : (2:ℝ≥0∞) ≠ 0)
    intro n
    change ‖((-2*I)^(k+1)*(δ n)^k/((k+1).factorial:ℂ))*unitIntervalMomentCoefficients f hf (k+1) n‖ ≤
      ‖(B:ℂ)*unitIntervalMomentCoefficients f hf (k+1) n‖
    rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg hB]
    exact mul_le_mul_of_nonneg_right (norm_latticeDifference_symbol_le δ k n) (norm_nonneg _)
  rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg hB] at hnorm
  exact hnorm.trans (mul_le_mul_of_nonneg_left (norm_unitIntervalMomentCoefficients_le f hf (k+1)) hB)

/-- The removable divided-difference moment series converges in L2
with bound 2*exp(2*norm(delta)) times the original coefficient norm. -/
theorem summable_boundedLatticeDifferenceTerm (f : ℝ → ℂ) (hf : Continuous f)
    (δ : NLS.Coeff ⊤) :
    Summable (fun k => ‖boundedLatticeDifferenceTerm f hf δ k‖) ∧
      ‖∑' k, boundedLatticeDifferenceTerm f hf δ k‖ ≤ (2*Real.exp (2*‖δ‖))*
        ‖unitIntervalMemLpCoefficients f (memLp_two_interval hf 0 1 (by norm_num))‖ := by
  let A := ‖unitIntervalMemLpCoefficients f (memLp_two_interval hf 0 1 (by norm_num))‖
  have he : HasSum (fun k : ℕ => (2*‖δ‖)^k/(k.factorial:ℝ)) (Real.exp (2*‖δ‖)) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp _
  have hs : Summable (fun k => ‖boundedLatticeDifferenceTerm f hf δ k‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (norm_boundedLatticeDifferenceTerm_le f hf δ) ((he.mul_left 2).summable.mul_right A)
  refine ⟨hs,(norm_tsum_le_tsum_norm hs).trans ?_⟩
  exact hasSum_le (norm_boundedLatticeDifferenceTerm_le f hf δ) hs.hasSum ((he.mul_left 2).mul_right A)

end NLS.Fourier
