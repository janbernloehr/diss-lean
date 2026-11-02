import NLS.SequenceSpaces.Convolution
import NLS.SequenceSpaces.Multiplier

/-! # Bounded matrices dominated by a summable convolution kernel

Sum the bounded shifted diagonal operators in operator norm. This realizes
the actual matrix entries on every Banach coefficient space, including
infinity, without assuming that the infinite matrix already acts boundedly.
-/
noncomputable section
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

private def matrixOffsetSymbol (A : ℤ → ℤ → ℂ) (b : Coeff 1)
    (hA : ∀ m n, ‖A m n‖ ≤ ‖b (m-n)‖) (d : ℤ) : Coeff ⊤ :=
  ⟨fun m => A m (m-d),memℓp_infty ⟨‖b d‖,by
    rintro _ ⟨m,rfl⟩
    simpa only [sub_sub_cancel] using hA m (m-d)⟩⟩

private theorem norm_matrixOffsetSymbol_le (A : ℤ → ℤ → ℂ) (b : Coeff 1)
    (hA : ∀ m n, ‖A m n‖ ≤ ‖b (m-n)‖) (d : ℤ) :
    ‖matrixOffsetSymbol A b hA d‖ ≤ ‖b d‖ := by
  apply lp.norm_le_of_forall_le (norm_nonneg _)
  intro m
  simpa only [matrixOffsetSymbol,sub_sub_cancel] using hA m (m-d)

private def matrixOffset (A : ℤ → ℤ → ℂ) (b : Coeff 1)
    (hA : ∀ m n, ‖A m n‖ ≤ ‖b (m-n)‖) (d : ℤ) : Coeff p →L[ℂ] Coeff p :=
  (multiplierCLM (matrixOffsetSymbol A b hA d)).comp
    (shift d).toContinuousLinearEquiv.toContinuousLinearMap

private theorem norm_matrixOffset_le (A : ℤ → ℤ → ℂ) (b : Coeff 1)
    (hA : ∀ m n, ‖A m n‖ ≤ ‖b (m-n)‖) (d : ℤ) :
    ‖matrixOffset (p := p) A b hA d‖ ≤ ‖b d‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro a
  calc
    _ ≤ ‖matrixOffsetSymbol A b hA d‖*‖shift d a‖ := norm_multiplier_le _ _
    _ ≤ ‖b d‖*‖a‖ := by
      rw [norm_shift]
      exact mul_le_mul_of_nonneg_right (norm_matrixOffsetSymbol_le A b hA d) (norm_nonneg _)

/-- The matrix is constructed as an absolutely convergent series of
shifted diagonals, with its convolution-majorant norm retained. -/
theorem exists_operator_of_convolution_dominated_matrix (A : ℤ → ℤ → ℂ) (b : Coeff 1)
    (hA : ∀ m n, ‖A m n‖ ≤ ‖b (m-n)‖) :
    ∃ T : Coeff p →L[ℂ] Coeff p, ‖T‖ ≤ ‖b‖ ∧
      ∀ m n : ℤ, (T (lp.single p n 1)) m = A m n := by
  let D : ℤ → Coeff p →L[ℂ] Coeff p := matrixOffset A b hA
  have hn : Summable (fun d => ‖D d‖) :=
    (lp.memℓp b).norm.summable_of_one.of_nonneg_of_le (fun _ => norm_nonneg _)
      (norm_matrixOffset_le A b hA)
  have hs : Summable D := hn.of_norm
  let T : Coeff p →L[ℂ] Coeff p := ∑' d, D d
  have hnorm : ‖T‖ ≤ ‖b‖ := by
    calc
      _ ≤ ∑' d, ‖D d‖ := norm_tsum_le_tsum_norm hn
      _ ≤ ∑' d, ‖b d‖ := hn.tsum_le_tsum (norm_matrixOffset_le A b hA)
        (lp.memℓp b).norm.summable_of_one
      _ = ‖b‖ := by simpa using (lp.hasSum_norm (p := 1) (by simp) b).tsum_eq
  refine ⟨T,hnorm,?_⟩
  intro m n
  let ev : (Coeff p →L[ℂ] Coeff p) →L[ℂ] ℂ :=
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p m).comp
      (ContinuousLinearMap.apply ℂ (Coeff p) (lp.single p n 1))
  change ev (∑' d, D d) = _
  rw [ContinuousLinearMap.map_tsum _ hs]
  have hterm (d : ℤ) : ev (D d) = if d = m-n then A m n else 0 := by
    change A m (m-d)*(lp.single p n (1 : ℂ) : Coeff p) (m-d) = _
    by_cases hd : d = m-n
    · subst d
      simp only [sub_sub_cancel,lp.single_apply,Pi.single_apply,ite_true,mul_one]
    · have hmn : m-d ≠ n := by omega
      simp only [lp.single_apply,Pi.single_apply,if_neg hmn,mul_zero,if_neg hd]
  simp_rw [hterm]
  exact tsum_ite_eq (m-n) (fun _ => A m n)

end NLS.Coeff
