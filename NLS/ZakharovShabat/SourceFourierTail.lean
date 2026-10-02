import NLS.ZakharovShabat.SourceWeightedPeriodOne
import NLS.SequenceSpaces.WeightedFourierTail

/-! # Fourier tails in the original source norm

Symmetric cutoffs commute with the period-one realization when the
physical cutoff is doubled. All identities preserve the exact
component-sum norm used in the spectral remainder estimates.
-/

noncomputable section
open Filter Topology
open scoped ENNReal
namespace NLS
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Period doubling also doubles a symmetric Fourier cutoff. -/
theorem Coeff.periodDouble_fourierTail (N : ℕ) (a : Coeff p) :
    Coeff.periodDouble (Coeff.fourierTail N a) = Coeff.fourierTail (2*N) (Coeff.periodDouble a) := by
  ext k
  by_cases hk : k % 2 = 0
  · have he : k = 2*(k/2) := by omega
    rw [he]
    simp only [Coeff.periodDouble_even, Coeff.fourierTail_apply, Int.natAbs_mul]
    have hiff : 2*N ≤ (2 : ℤ).natAbs*(k/2).natAbs ↔ N ≤ (k/2).natAbs := by norm_num
    simp only [hiff]
  · have he : k = 2*(k/2)+1 := by omega
    rw [he,Coeff.fourierTail_apply,Coeff.periodDouble_odd,Coeff.periodDouble_odd]
    split_ifs <;> rfl

namespace ZakharovShabat

/-- Both source components retain the boundary frequencies `|n| = N`. -/
def sourceFourierTail (N : ℕ) (φ : CoeffPair p) : CoeffPair p :=
  (CoeffPair.toMax p).symm (Coeff.fourierTail N φ.fst, Coeff.fourierTail N φ.snd)

@[simp] theorem sourceFourierTail_fst (N : ℕ) (φ : CoeffPair p) (n : ℤ) :
    (sourceFourierTail N φ).fst n = if N ≤ n.natAbs then φ.fst n else 0 :=
  Coeff.fourierTail_apply N φ.fst n

@[simp] theorem sourceFourierTail_snd (N : ℕ) (φ : CoeffPair p) (n : ℤ) :
    (sourceFourierTail N φ).snd n = if N ≤ n.natAbs then φ.snd n else 0 :=
  Coeff.fourierTail_apply N φ.snd n

theorem tendsto_sourceFourierTail (hp : p ≠ ⊤) (φ : CoeffPair p) :
    Tendsto (fun N : ℕ => sourceFourierTail N φ) atTop (𝓝 0) := by
  exact ((CoeffPair.toMax p).symm.continuous.tendsto 0).comp
    ((Coeff.tendsto_fourierTail hp φ.fst).prodMk_nhds (Coeff.tendsto_fourierTail hp φ.snd))

theorem norm_sourceFourierTail_antitone (hp : p ≠ ⊤) (φ : CoeffPair p) :
    Antitone (fun N : ℕ => ‖sourceFourierTail N φ‖) := by
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans_le Fact.out)) hp
  intro M N hMN
  apply (Real.rpow_le_rpow_iff (norm_nonneg _) (norm_nonneg _) hp0).mp
  rw [norm_withLp_prod_rpow hp,norm_withLp_prod_rpow hp]
  exact add_le_add
    (Real.rpow_le_rpow (norm_nonneg _) (Coeff.norm_fourierTail_antitone (ne_of_gt (zero_lt_one.trans_le Fact.out)) φ.fst hMN) ENNReal.toReal_nonneg)
    (Real.rpow_le_rpow (norm_nonneg _) (Coeff.norm_fourierTail_antitone (ne_of_gt (zero_lt_one.trans_le Fact.out)) φ.snd hMN) ENNReal.toReal_nonneg)

/-- The physical tail at `2N` is the isometric image of the source tail at `N`. -/
theorem weightedPairFourierTail_sourceWeightedPeriodOne (N : ℕ) (φ : CoeffPair p) :
    weightedPairFourierTail SpectralWeight.one.toWeight (2*N) (sourceWeightedPeriodOne φ) =
      sourceWeightedPeriodOne (sourceFourierTail N φ) := by
  apply weightedPair_ext <;> intro k
  · simp only [weightedPairFourierTail_fst, WeightedCoeff.fourierTail_apply, sourceWeightedPeriodOne_fst]
    change (if 2*N ≤ k.natAbs then Coeff.periodDouble φ.fst k else 0) =
      Coeff.periodDouble (Coeff.fourierTail N φ.fst) k
    simpa only [Coeff.fourierTail_apply] using
      (congrArg (fun a : Coeff p => a k) (Coeff.periodDouble_fourierTail N φ.fst)).symm
  · simp only [weightedPairFourierTail_snd, WeightedCoeff.fourierTail_apply, sourceWeightedPeriodOne_snd]
    change (if 2*N ≤ k.natAbs then Coeff.periodDouble φ.snd k else 0) =
      Coeff.periodDouble (Coeff.fourierTail N φ.snd) k
    simpa only [Coeff.fourierTail_apply] using
      (congrArg (fun a : Coeff p => a k) (Coeff.periodDouble_fourierTail N φ.snd)).symm

@[simp] theorem norm_weightedPairFourierTail_sourceWeightedPeriodOne (N : ℕ) (φ : CoeffPair p) :
    ‖weightedPairFourierTail SpectralWeight.one.toWeight (2*N) (sourceWeightedPeriodOne φ)‖ =
      ‖sourceFourierTail N φ‖ := by
  rw [weightedPairFourierTail_sourceWeightedPeriodOne,norm_sourceWeightedPeriodOne]

end ZakharovShabat
end NLS
