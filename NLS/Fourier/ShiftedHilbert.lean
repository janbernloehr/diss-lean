import NLS.ZakharovShabat.HilbertIntervalExtension

/-!
# The shifted discrete Hilbert kernel on `ℓ2`

Odd Fourier coefficients of the normalized interval extension produce the
kernel `2 / (π (2k-2n-1))`. The resulting operator is bounded on all `ℓ2`,
with its finite-input formula proved from the physical interval integrals.
The bound here is sufficient, not asserted to be the optimal constant.
-/

noncomputable section
open Complex
open scoped ENNReal
namespace NLS.Fourier
open NLS.ZakharovShabat NLS.ZakharovShabat.BoundaryCondition

private theorem oddIndex_injective : Function.Injective (fun n : ℤ => 2 * n + 1) := by
  intro m n h
  dsimp at h
  omega

/-- Restrict a Hilbert sequence to its odd indices and reindex by the integers. -/
def oddSample : Coeff 2 →ₗ[ℂ] Coeff 2 where
  toFun a := ⟨fun n => a (2 * n + 1), by
    change Memℓp (fun n : ℤ => a (2 * n + 1)) 2
    rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    exact (a.property.summable (by norm_num)).comp_injective oddIndex_injective⟩
  map_add' _ _ := lp.ext rfl
  map_smul' _ _ := lp.ext rfl

@[simp] theorem oddSample_apply (a : Coeff 2) (n : ℤ) : oddSample a n = a (2 * n + 1) := rfl

theorem norm_oddSample_le (a : Coeff 2) : ‖oddSample a‖ ≤ ‖a‖ := by
  apply lp.norm_le_of_tsum_le (by norm_num) (norm_nonneg a)
  rw [lp.norm_rpow_eq_tsum (by norm_num)]
  exact tsum_comp_le_tsum_of_inj (a.property.summable (by norm_num))
    (fun n => by positivity) oddIndex_injective

/-- Odd-index restriction is a contraction. -/
def oddSampleCLM : Coeff 2 →L[ℂ] Coeff 2 := oddSample.mkContinuous 1 (by simpa using norm_oddSample_le)

@[simp] theorem oddSampleCLM_apply (a : Coeff 2) : oddSampleCLM a = oddSample a := rfl

/-- The shifted discrete Hilbert transform, normalized by `1/π`. -/
def shiftedHilbert : Coeff 2 →L[ℂ] Coeff 2 :=
  (-2 * I : ℂ) • oddSampleCLM.comp
    ((ContinuousLinearMap.snd ℂ (Coeff 2) (Coeff 2)).comp
      ((hilbertIntervalExtension .dirichlet).comp (ContinuousLinearMap.inr ℂ (Coeff 2) (Coeff 2))))

theorem shiftedHilbert_apply (a : Coeff 2) (n : ℤ) :
    shiftedHilbert a n = (-2 * I) * (hilbertIntervalExtension .dirichlet (0, a)).2 (2 * n + 1) := rfl

/-- A uniform Hilbert-space bound, independent of support size. -/
theorem norm_shiftedHilbert_apply_le (a : Coeff 2) : ‖shiftedHilbert a‖ ≤ 2 * ‖a‖ := by
  change ‖(-2 * I : ℂ) • oddSample ((hilbertIntervalExtension .dirichlet (0, a)).2)‖ ≤ _
  rw [norm_smul]
  have hn : ‖(-2 * I : ℂ)‖ = 2 := by norm_num [norm_mul]
  rw [hn]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  calc
    _ ≤ ‖(hilbertIntervalExtension .dirichlet (0, a)).2‖ := norm_oddSample_le _
    _ ≤ ‖hilbertIntervalExtension .dirichlet (0, a)‖ := norm_snd_le _
    _ ≤ ‖a‖ := by simpa using norm_hilbertIntervalExtension_apply_le .dirichlet (0, a)

theorem norm_shiftedHilbert_le : ‖shiftedHilbert‖ ≤ 2 :=
  shiftedHilbert.opNorm_le_bound (by norm_num) norm_shiftedHilbert_apply_le

/-- The bounded operator has exactly the shifted reciprocal kernel on finite input. -/
theorem shiftedHilbert_finite (a : ℤ →₀ ℂ) (n : ℤ) :
    shiftedHilbert (Coeff.ofFinsupp a) n =
      a.sum (fun k z => z * (2 / ((Real.pi : ℂ) * (2 * k - 2 * n - 1)))) := by
  rw [shiftedHilbert_apply]
  have he : ((0 : Coeff 2), Coeff.ofFinsupp a) = finitePairCoeffs (0, a) := by simp
  rw [he, hilbertIntervalExtension_finite, finiteIntervalExtension_snd,
    finiteIntervalAmplitude_apply, intervalAmplitude_odd]
  simp only [Finsupp.sum_zero_index, mul_zero, add_zero, extensionSign]
  unfold Finsupp.sum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hz (w : ℂ) : (-2 * I) * (w * (I / ((Real.pi : ℂ) * (2 * k - 2 * n - 1)))) =
      w * (2 / ((Real.pi : ℂ) * (2 * k - 2 * n - 1))) := by
    calc
      _ = (-2 * (I * I)) * w / ((Real.pi : ℂ) * (2 * k - 2 * n - 1)) := by ring
      _ = _ := by rw [I_mul_I]; ring
  exact hz (a k)

end NLS.Fourier
