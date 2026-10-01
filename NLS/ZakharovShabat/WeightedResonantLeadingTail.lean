import NLS.SequenceSpaces.FunctionOrZero
import NLS.ZakharovShabat.ResonantLeadingPowerTail

/-!
# The signed weighted leading Fourier tail

Sampling the two physical Fourier components at `-2n` and `2n`, with
weight `w(2n)`, gives a continuous linear map into the component-sum
`ℓᵖ` pair space. Its norm is controlled by the original weighted
Fourier tail at `2N`, with constant one.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The signed leading coefficient, weighted and cut off in the
resonance index. The negative component is selected by `false`. -/
def weightedResonantLeadingTailCoordinate (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (N : ℕ) (positive : Bool) (n : ℤ) : ℂ :=
  if N ≤ n.natAbs then
    (w (2*n) : ℂ)*(if positive then φ.snd.val (2*n) else φ.fst.val (-(2*n)))
  else 0

/-- The leading tail as a pair with the original component-sum norm. -/
def weightedResonantLeadingTail (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (N : ℕ) : CoeffPair p :=
  WithLp.toLp p
    (Coeff.ofFunctionOrZero p (weightedResonantLeadingTailCoordinate w φ N false),
      Coeff.ofFunctionOrZero p (weightedResonantLeadingTailCoordinate w φ N true))

/-- The actual source coefficients make both sampled tails belong
to the sequence space for every cutoff, including zero. -/
theorem weightedResonantLeadingTailCoordinate_mem (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (N : ℕ) (positive : Bool) :
    Memℓp (weightedResonantLeadingTailCoordinate w φ N positive) p := by
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos
    (ne_of_gt (zero_lt_one.trans_le (Fact.out : 1 ≤ p))) hp
  have hs := (resonantLeadingPower_tail_summable_and_le hp w φ N 0 (by omega)).1
  apply Coeff.memℓp_of_power_dominated _ _ hs
  intro n
  by_cases hn : N ≤ n.natAbs
  · cases positive
    · simpa only [weightedResonantLeadingTailCoordinate,if_pos hn,Bool.false_eq_true,if_false,
        norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (w.positive _),resonantLeadingPower] using
        le_add_of_nonneg_right (Real.rpow_nonneg (mul_nonneg (w.positive _).le (norm_nonneg _)) p.toReal)
    · simpa only [weightedResonantLeadingTailCoordinate,if_pos hn,if_true,
        norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (w.positive _),resonantLeadingPower] using
        le_add_of_nonneg_left (Real.rpow_nonneg (mul_nonneg (w.positive _).le (norm_nonneg _)) p.toReal)
  · simp only [weightedResonantLeadingTailCoordinate,if_neg hn,norm_zero,Real.zero_rpow hp0.ne',le_refl]

/-- The negative component retains the original signed coefficient. -/
theorem weightedResonantLeadingTail_fst (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (N : ℕ) (n : ℤ) :
    (weightedResonantLeadingTail w φ N).fst n =
      if N ≤ n.natAbs then (w (2*n) : ℂ)*φ.fst.val (-(2*n)) else 0 := by
  exact Coeff.ofFunctionOrZero_apply_of_mem p _
    (weightedResonantLeadingTailCoordinate_mem hp w φ N false) n

/-- The positive component retains the original signed coefficient. -/
theorem weightedResonantLeadingTail_snd (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (N : ℕ) (n : ℤ) :
    (weightedResonantLeadingTail w φ N).snd n =
      if N ≤ n.natAbs then (w (2*n) : ℂ)*φ.snd.val (2*n) else 0 := by
  exact Coeff.ofFunctionOrZero_apply_of_mem p _
    (weightedResonantLeadingTailCoordinate_mem hp w φ N true) n

/-- The leading pair is bounded by the exact source Fourier tail,
with no loss from combining its two components. -/
theorem norm_weightedResonantLeadingTail_le (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (N : ℕ) :
    ‖weightedResonantLeadingTail w φ N‖ ≤ ‖weightedPairFourierTail w.toWeight (2*N) φ‖ := by
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos
    (ne_of_gt (zero_lt_one.trans_le (Fact.out : 1 ≤ p))) hp
  apply (Real.rpow_le_rpow_iff (norm_nonneg _) (norm_nonneg _) hp0).mp
  have heq : ‖weightedResonantLeadingTail w φ N‖^p.toReal =
      ∑' n : ℤ, if N ≤ n.natAbs then resonantLeadingPower w φ n else 0 := by
    rw [CoeffPair.norm_rpow_eq_tsum hp]
    apply tsum_congr
    intro n
    by_cases hn : N ≤ n.natAbs <;>
      simp [weightedResonantLeadingTail_fst hp,weightedResonantLeadingTail_snd hp,hn,
        Complex.norm_real,Real.norm_eq_abs,abs_of_pos (w.positive _),resonantLeadingPower,
        norm_zero,Real.zero_rpow hp0.ne']
  rw [heq]
  exact (resonantLeadingPower_tail_summable_and_le hp w φ N (2*N) le_rfl).2

/-- Sampling the leading Fourier tail is continuous and complex
linear, with operator norm at most one for every cutoff. -/
def weightedResonantLeadingTailCLM (hp : p ≠ ⊤) (w : SpectralWeight) (N : ℕ) :
    WeightedCoeffPair w.toWeight p →L[ℂ] CoeffPair p :=
  LinearMap.mkContinuous
    { toFun := fun φ => weightedResonantLeadingTail w φ N
      map_add' := by
        intro φ ψ
        apply (CoeffPair.toMax p).injective
        apply Prod.ext <;> ext n <;> by_cases hn : N ≤ n.natAbs <;>
          simp [weightedResonantLeadingTail_fst hp,weightedResonantLeadingTail_snd hp,hn,mul_add]
      map_smul' := by
        intro c φ
        apply (CoeffPair.toMax p).injective
        apply Prod.ext <;> ext n <;> by_cases hn : N ≤ n.natAbs <;>
          simp [weightedResonantLeadingTail_fst hp,weightedResonantLeadingTail_snd hp,hn,mul_left_comm] }
    1 (fun φ => by
      change ‖weightedResonantLeadingTail w φ N‖ ≤ 1*‖φ‖
      simpa only [one_mul] using (norm_weightedResonantLeadingTail_le hp w φ N).trans
        (norm_weightedPairFourierTail_le hp w.toWeight (2*N) φ))

@[simp] theorem weightedResonantLeadingTailCLM_apply (hp : p ≠ ⊤) (w : SpectralWeight)
    (N : ℕ) (φ : WeightedCoeffPair w.toWeight p) :
    weightedResonantLeadingTailCLM hp w N φ = weightedResonantLeadingTail w φ N := rfl

end NLS.ZakharovShabat
