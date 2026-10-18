import NLS.Fourier.UnitIntervalFourierMoments
import Mathlib.Analysis.SpecialFunctions.Exponential

/-! # L2 convergence of bounded-displacement Fourier moment series

The actual Taylor-moment sequence has an exponential L2 bound for arbitrary bounded complex displacements. Identification of its sum with the sampled integrals is a separate obligation.
-/

noncomputable section
open Set Complex MeasureTheory
open scoped ENNReal
namespace NLS.Fourier

private theorem norm_latticeMoment_symbol_le (δ : NLS.Coeff ⊤) (k : ℕ) (n : ℤ) :
    ‖(-2*I*δ n)^k/(k.factorial:ℂ)‖ ≤ (2*‖δ‖)^k/(k.factorial:ℝ) := by
  simp only [norm_div,norm_pow,norm_mul,norm_neg,norm_ofNat,norm_I,mul_one,Complex.norm_natCast]
  gcongr
  exact lp.norm_apply_le_norm (by simp) δ n

/-- The kth Taylor moment of a Fourier sampling displacement, as an
actual L2 sequence for any bounded complex displacement sequence. -/
def boundedLatticeMomentTerm (f : ℝ → ℂ) (hf : Continuous f)
    (δ : NLS.Coeff ⊤) (k : ℕ) : NLS.Coeff 2 :=
  ⟨fun n => ((-2*I*δ n)^k/(k.factorial:ℂ))*unitIntervalMomentCoefficients f hf k n, by
    apply ((lp.memℓp (unitIntervalMomentCoefficients f hf k)).norm.const_mul
      ((2*‖δ‖)^k/(k.factorial:ℝ))).mono
    intro n
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (norm_latticeMoment_symbol_le δ k n) (norm_nonneg _)⟩

@[simp] theorem boundedLatticeMomentTerm_apply (f : ℝ → ℂ) (hf : Continuous f)
    (δ : NLS.Coeff ⊤) (k : ℕ) (n : ℤ) :
    boundedLatticeMomentTerm f hf δ k n =
      ((-2*I*δ n)^k/(k.factorial:ℂ))*periodOneCoefficient (fun x => (x:ℂ)^k*f x) n := by
  simp only [boundedLatticeMomentTerm,unitIntervalMomentCoefficients_apply]

/-- The factorial moment bound uses the physical L2 norm alone. -/
theorem norm_boundedLatticeMomentTerm_le (f : ℝ → ℂ) (hf : Continuous f)
    (δ : NLS.Coeff ⊤) (k : ℕ) :
    ‖boundedLatticeMomentTerm f hf δ k‖ ≤ (2*‖δ‖)^k/(k.factorial:ℝ)*
      ‖unitIntervalMemLpCoefficients f (memLp_two_interval hf 0 1 (by norm_num))‖ := by
  let B : ℝ := (2*‖δ‖)^k/(k.factorial:ℝ)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hnorm : ‖boundedLatticeMomentTerm f hf δ k‖ ≤
      ‖(B:ℂ) • unitIntervalMomentCoefficients f hf k‖ := by
    apply lp.norm_mono (by norm_num : (2:ℝ≥0∞) ≠ 0)
    intro n
    change ‖((-2*I*δ n)^k/(k.factorial:ℂ))*unitIntervalMomentCoefficients f hf k n‖ ≤
      ‖(B:ℂ)*unitIntervalMomentCoefficients f hf k n‖
    rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg hB]
    exact mul_le_mul_of_nonneg_right (norm_latticeMoment_symbol_le δ k n) (norm_nonneg _)
  rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg hB] at hnorm
  exact hnorm.trans (mul_le_mul_of_nonneg_left (norm_unitIntervalMomentCoefficients_le f hf k) hB)

/-- The full moment series converges in L2 with exponential dependence
only on the supremum norm of the complex spectral displacements. -/
theorem summable_boundedLatticeMomentTerm (f : ℝ → ℂ) (hf : Continuous f)
    (δ : NLS.Coeff ⊤) :
    Summable (fun k => ‖boundedLatticeMomentTerm f hf δ k‖) ∧
      ‖∑' k, boundedLatticeMomentTerm f hf δ k‖ ≤ Real.exp (2*‖δ‖)*
        ‖unitIntervalMemLpCoefficients f (memLp_two_interval hf 0 1 (by norm_num))‖ := by
  let A := ‖unitIntervalMemLpCoefficients f (memLp_two_interval hf 0 1 (by norm_num))‖
  have he : HasSum (fun k : ℕ => (2*‖δ‖)^k/(k.factorial:ℝ)) (Real.exp (2*‖δ‖)) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp _
  have hs : Summable (fun k => ‖boundedLatticeMomentTerm f hf δ k‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (norm_boundedLatticeMomentTerm_le f hf δ) (he.summable.mul_right A)
  refine ⟨hs,(norm_tsum_le_tsum_norm hs).trans ?_⟩
  exact hasSum_le (norm_boundedLatticeMomentTerm_le f hf δ) hs.hasSum (he.mul_right A)

end NLS.Fourier
