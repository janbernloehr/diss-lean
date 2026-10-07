import NLS.ZakharovShabat.NormalizedWeightedClosingInverseSupport
import NLS.SequenceSpaces.Multiplier

/-! # Finite weighted targets for the actual closing inverse

Weighting a finite block is a bounded linear map even when the full
weight is unbounded. Decoding gives the exact original Fourier truncation,
and finite-gap base points have these targets at every large cutoff.
-/
noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

private def finiteWeightSymbol (w : SpectralWeight) (N : ℕ) : Coeff ⊤ :=
  ∑ n ∈ Finset.Ioo (-(N : ℤ)) N, lp.single ⊤ n (w (2*n) : ℂ)

private theorem finiteWeightSymbol_apply (w : SpectralWeight) (N : ℕ) (n : ℤ) :
    finiteWeightSymbol w N n = if n ∈ Finset.Ioo (-(N : ℤ)) N then (w (2*n) : ℂ) else 0 := by
  change (lp.evalₗ (𝕜 := ℂ) (fun _ : ℤ => ℂ) ⊤ n)
    (∑ i ∈ Finset.Ioo (-(N : ℤ)) N, lp.single ⊤ i (w (2*i) : ℂ)) = _
  rw [map_sum]
  simp [lp.evalₗ_apply, lp.single_apply, Pi.single_apply]

/-- Weight only the finite block of original source coefficients. -/
def normalizedWeightedTruncateCLM (w : SpectralWeight) (N : ℕ) : CoeffPair p →L[ℂ] CoeffPair p :=
  (CoeffPair.toMax p).symm.toContinuousLinearMap.comp
    (((Coeff.multiplierCLM (finiteWeightSymbol w N)).prodMap
      (Coeff.multiplierCLM (finiteWeightSymbol w N))).comp (CoeffPair.toMax p).toContinuousLinearMap)

@[simp] theorem normalizedWeightedTruncateCLM_fst (w : SpectralWeight) (N : ℕ) (φ : CoeffPair p) (n : ℤ) :
    (normalizedWeightedTruncateCLM w N φ).fst n =
      if n ∈ Finset.Ioo (-(N : ℤ)) N then (w (2*n) : ℂ)*φ.fst n else 0 := by
  change finiteWeightSymbol w N n * φ.fst n = _
  rw [finiteWeightSymbol_apply]
  split_ifs <;> simp

@[simp] theorem normalizedWeightedTruncateCLM_snd (w : SpectralWeight) (N : ℕ) (φ : CoeffPair p) (n : ℤ) :
    (normalizedWeightedTruncateCLM w N φ).snd n =
      if n ∈ Finset.Ioo (-(N : ℤ)) N then (w (2*n) : ℂ)*φ.snd n else 0 := by
  change finiteWeightSymbol w N n * φ.snd n = _
  rw [finiteWeightSymbol_apply]
  split_ifs <;> simp

/-- The constructed target has literally zero high Fourier coefficients. -/
theorem normalizedWeightedTruncateCLM_support (w : SpectralWeight) (N : ℕ) (φ : CoeffPair p)
    (n : ℤ) (hn : N ≤ n.natAbs) :
    (normalizedWeightedTruncateCLM w N φ).fst n = 0 ∧
    (normalizedWeightedTruncateCLM w N φ).snd n = 0 := by
  have hout : n ∉ Finset.Ioo (-(N : ℤ)) N := by simp only [Finset.mem_Ioo]; omega
  simp only [normalizedWeightedTruncateCLM_fst, normalizedWeightedTruncateCLM_snd, if_neg hout, and_self]

/-- Real original sources give real finite weighted targets. -/
theorem normalizedWeightedTruncateCLM_realType (w : SpectralWeight) (N : ℕ) (φ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p φ)) :
    IsRealType (CoeffPair.toMax p (normalizedWeightedTruncateCLM w N φ)) := by
  intro n
  change (normalizedWeightedTruncateCLM w N φ).snd n =
    (starRingEnd ℂ) ((normalizedWeightedTruncateCLM w N φ).fst (-n))
  have hneg : -n ∈ Finset.Ioo (-(N : ℤ)) N ↔ n ∈ Finset.Ioo (-(N : ℤ)) N := by
    simp only [Finset.mem_Ioo]; omega
  simp only [normalizedWeightedTruncateCLM_fst, normalizedWeightedTruncateCLM_snd, hneg]
  split_ifs
  · rw [map_mul, mul_neg, SpectralWeight.apply_neg, Complex.conj_ofReal]
    exact congrArg (fun z : ℂ => (w (2*n) : ℂ)*z) (hreal n)
  · exact (map_zero _).symm

/-- Decoding the finite target gives the exact original low Fourier block. -/
theorem normalizedWeightedSource_truncate (w : SpectralWeight) (N : ℕ) (φ : CoeffPair p) :
    normalizedWeightedSource w (normalizedWeightedTruncateCLM w N φ) =
      (CoeffPair.toMax p).symm
        (Coeff.truncate (Finset.Ioo (-(N : ℤ)) N) φ.fst,
         Coeff.truncate (Finset.Ioo (-(N : ℤ)) N) φ.snd) := by
  apply (CoeffPair.toMax p).injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  apply Prod.ext <;> ext n
  · change (normalizedWeightedSource _ _).fst n = _
    rw [normalizedWeightedSource_fst, normalizedWeightedTruncateCLM_fst, Coeff.truncate_apply]
    split_ifs
    · exact mul_div_cancel_left₀ _ (w.toWeight.complex_ne_zero _)
    · exact zero_div _
  · change (normalizedWeightedSource _ _).snd n = _
    rw [normalizedWeightedSource_snd, normalizedWeightedTruncateCLM_snd, Coeff.truncate_apply]
    split_ifs
    · exact mul_div_cancel_left₀ _ (w.toWeight.complex_ne_zero _)
    · exact zero_div _

/-- A finite-gap weighted base point has its actual finite weighted target
at every sufficiently large cutoff. -/
theorem exists_normalizedWeightedClosingMap_eq_truncate_of_finiteGap
    (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight) (φ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p φ))
    (hf : (⟨normalizedWeightedSource w φ, normalizedWeightedSource_realType w φ hreal⟩ : realTypeSourceLocus p)
      ∈ sourceFiniteGapLocus hp hp1) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ M : ℕ, N ≤ M →
      normalizedWeightedClosingMap hp w φ M = normalizedWeightedTruncateCLM w M (normalizedWeightedSource w φ) := by
  obtain ⟨N,hN,hclosed⟩ := exists_sourceFiniteGap_weighted_center_closed hp hp1 _ hf w
    (normalizedWeightedPeriodOne w φ) (forget_normalizedWeightedPeriodOne w φ)
  obtain ⟨r,hr,K,hK,hD⟩ := exists_fixedBall_normalizedWeightedClosingMap_derivative hp hp1 w φ 1 (by norm_num)
  refine ⟨max N K,by omega,?_⟩
  intro M hM
  have hmem := ((hD M (by omega)).2.1 φ (mem_ball_self (by positivity))).1
  have hcoord := normalizedWeightedClosingMap_apply_of_mem hp w φ M hmem
  apply (CoeffPair.toMax p).injective
  apply Prod.ext <;> ext n
  · change (normalizedWeightedClosingMap hp w φ M).fst n = (normalizedWeightedTruncateCLM w M _).fst n
    rw [(hcoord n).1, normalizedWeightedTruncateCLM_fst, normalizedWeightedSource_fst]
    by_cases hn : M ≤ n.natAbs
    · have hout : n ∉ Finset.Ioo (-(M : ℤ)) M := by simp only [Finset.mem_Ioo]; omega
      rw [if_pos hn,if_neg hout,(hclosed (-n) (by rw [Int.natAbs_neg]; omega)).2,mul_zero]
    · have hin : n ∈ Finset.Ioo (-(M : ℤ)) M := by simp only [Finset.mem_Ioo]; omega
      rw [if_neg hn,if_pos hin,mul_div_cancel₀ _ (w.toWeight.complex_ne_zero _)]
  · change (normalizedWeightedClosingMap hp w φ M).snd n = (normalizedWeightedTruncateCLM w M _).snd n
    rw [(hcoord n).2, normalizedWeightedTruncateCLM_snd, normalizedWeightedSource_snd]
    by_cases hn : M ≤ n.natAbs
    · have hout : n ∉ Finset.Ioo (-(M : ℤ)) M := by simp only [Finset.mem_Ioo]; omega
      rw [if_pos hn,if_neg hout,(hclosed n (by omega)).1,mul_zero]
    · have hin : n ∈ Finset.Ioo (-(M : ℤ)) M := by simp only [Finset.mem_Ioo]; omega
      rw [if_neg hn,if_pos hin,mul_div_cancel₀ _ (w.toWeight.complex_ne_zero _)]

end NLS.ZakharovShabat
