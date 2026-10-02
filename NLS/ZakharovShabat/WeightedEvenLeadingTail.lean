import NLS.ZakharovShabat.WeightedResonantLeadingTail
import NLS.SequenceSpaces.PeriodDoubling
import NLS.SequenceSpaces.Reflection

/-! # Exact leading-tail norm for period-one weighted potentials

For an even physical Fourier sequence, sampling the resonant leading
coefficients loses no modes. The first component is reflected, an
isometry because spectral weights are symmetric.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Even physical support upgrades the leading-tail contraction to
an exact norm identity, with physical cutoff twice the resonance cutoff. -/
theorem norm_weightedResonantLeadingTail_eq_of_even
    (hp : p ≠ ⊤) (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight p)
    (heven : ∀ k : ℤ, φ.fst.val (2*k+1) = 0 ∧ φ.snd.val (2*k+1) = 0) (N : ℕ) :
    ‖weightedResonantLeadingTail w φ N‖ = ‖weightedPairFourierTail w.toWeight (2*N) φ‖ := by
  have hfst : Coeff.periodDouble (Coeff.reflection (weightedResonantLeadingTail w φ N).fst) =
      WeightedCoeff.weightEquiv w.toWeight p (WeightedCoeff.fourierTail w.toWeight (2*N) φ.fst) := by
    ext k
    by_cases hk : k % 2 = 0
    · have he : k = 2*(k/2) := by omega
      rw [he,Coeff.periodDouble_even]
      simp [Coeff.reflection_apply, weightedResonantLeadingTail_fst hp,
        WeightedCoeff.weightEquiv_apply, WeightedCoeff.fourierTail_apply, Int.natAbs_mul]
    · have he : k = 2*(k/2)+1 := by omega
      rw [he,Coeff.periodDouble_odd]
      simp [WeightedCoeff.weightEquiv_apply,WeightedCoeff.fourierTail_apply,(heven (k/2)).1]
  have hsnd : Coeff.periodDouble (weightedResonantLeadingTail w φ N).snd =
      WeightedCoeff.weightEquiv w.toWeight p (WeightedCoeff.fourierTail w.toWeight (2*N) φ.snd) := by
    ext k
    by_cases hk : k % 2 = 0
    · have he : k = 2*(k/2) := by omega
      rw [he,Coeff.periodDouble_even]
      simp [weightedResonantLeadingTail_snd hp,
        WeightedCoeff.weightEquiv_apply, WeightedCoeff.fourierTail_apply, Int.natAbs_mul]
    · have he : k = 2*(k/2)+1 := by omega
      rw [he,Coeff.periodDouble_odd]
      simp [WeightedCoeff.weightEquiv_apply,WeightedCoeff.fourierTail_apply,(heven (k/2)).2]
  have hf : ‖(weightedResonantLeadingTail w φ N).fst‖ =
      ‖WeightedCoeff.fourierTail w.toWeight (2*N) φ.fst‖ := by
    rw [WeightedCoeff.norm_eq, ← hfst, Coeff.norm_periodDouble, Coeff.reflection.norm_map]
  have hg : ‖(weightedResonantLeadingTail w φ N).snd‖ =
      ‖WeightedCoeff.fourierTail w.toWeight (2*N) φ.snd‖ := by
    rw [WeightedCoeff.norm_eq, ← hsnd, Coeff.norm_periodDouble]
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos
    (ne_of_gt (zero_lt_one.trans_le (Fact.out : 1 ≤ p))) hp
  apply (Real.rpow_left_inj (norm_nonneg _) (norm_nonneg _) hp0.ne').mp
  rw [norm_withLp_prod_rpow hp,norm_withLp_prod_rpow hp,hf,hg]
  rfl

end NLS.ZakharovShabat
