import NLS.ZakharovShabat.SourceHigherSobolevEmbedding
import NLS.ZakharovShabat.SobolevJetNormBounds

/-! # Exact physical Sobolev coordinates on every original H^m source

At order k the coefficients are multiplied by ⟨2nπ⟩^k. The component-sum
Hilbert norm is the dissertation's norm, without an equivalent-norm replacement.
-/
noncomputable section
namespace NLS.ZakharovShabat

private def sourcePiWeight (k : ℕ) : Weight :=
  ⟨fun n => (SpectralWeight.piSobolev k (Nat.cast_nonneg k)) (2*n),
    fun n => (SpectralWeight.piSobolev k (Nat.cast_nonneg k)).positive (2*n)⟩

private theorem sourcePiWeight_apply (k : ℕ) (n : ℤ) :
    sourcePiWeight k n = (1+2*Real.pi*|(n:ℝ)|)^k := by
  simp [sourcePiWeight, SpectralWeight.piSobolev_apply, abs_mul, Real.rpow_natCast,
    abs_of_pos Real.pi_pos, mul_comm, mul_left_comm]

/-- Weighted scalar coordinates at any lower integer regularity. -/
def sourcePiSobolevScalar (m k : ℕ) (hk : k ≤ m) (a : ScalarSobolev m) : Coeff 2 :=
  WeightedCoeff.weightEquiv (sourcePiWeight k) 2
    (WeightedCoeff.weightedMultiplier (Weight.sobolev m) (sourcePiWeight k)
      (fun _ => 1) ((2*Real.pi)^k) (by
        intro n
        simp only [norm_one, mul_one, sourcePiWeight_apply, Weight.sobolev_apply, Real.rpow_natCast]
        calc
          _ ≤ ((2*Real.pi)*(1+|(n:ℝ)|))^k := by
            apply pow_le_pow_left₀ (by positivity)
            nlinarith [Real.pi_gt_three]
          _ = (2*Real.pi)^k*(1+|(n:ℝ)|)^k := mul_pow _ _ _
          _ ≤ _ := mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ (by linarith [abs_nonneg (n:ℝ)]) hk) (by positivity)) a)

@[simp] theorem sourcePiSobolevScalar_apply (m k : ℕ) (hk : k ≤ m)
    (a : ScalarSobolev m) (n : ℤ) :
    sourcePiSobolevScalar m k hk a n =
      ((SpectralWeight.piSobolev k (Nat.cast_nonneg k)) (2*n) : ℂ)*a.val n := by
  change ((SpectralWeight.piSobolev k (Nat.cast_nonneg k)) (2*n) : ℂ)*(1*a.val n) = _
  rw [one_mul]

/-- The physical pair norm is the norm of these actual weighted coefficients. -/
def sourcePiSobolevCoordinates (m k : ℕ) (hk : k ≤ m) (a : SobolevSource m) : CoeffPair 2 :=
  WithLp.toLp 2 (sourcePiSobolevScalar m k hk a.1, sourcePiSobolevScalar m k hk a.2)

@[simp] theorem sourcePiSobolevCoordinates_fst (m k : ℕ) (hk : k ≤ m)
    (a : SobolevSource m) (n : ℤ) :
    (sourcePiSobolevCoordinates m k hk a).fst n =
      ((SpectralWeight.piSobolev k (Nat.cast_nonneg k)) (2*n) : ℂ)*a.1.val n :=
  sourcePiSobolevScalar_apply m k hk a.1 n

@[simp] theorem sourcePiSobolevCoordinates_snd (m k : ℕ) (hk : k ≤ m)
    (a : SobolevSource m) (n : ℤ) :
    (sourcePiSobolevCoordinates m k hk a).snd n =
      ((SpectralWeight.piSobolev k (Nat.cast_nonneg k)) (2*n) : ℂ)*a.2.val n :=
  sourcePiSobolevScalar_apply m k hk a.2 n

/-- Exact physical Fourier energy, including both components. -/
theorem sourcePiSobolevCoordinates_norm_sq (m k : ℕ) (hk : k ≤ m) (a : SobolevSource m) :
    ‖sourcePiSobolevCoordinates m k hk a‖^2 =
      ∑' n : ℤ, (1+|((2*n:ℤ):ℝ)*Real.pi|)^(2*k)*
        (‖a.1.val n‖^2+‖a.2.val n‖^2) := by
  have h := CoeffPair.norm_rpow_eq_tsum (by simp) (sourcePiSobolevCoordinates m k hk a)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h
  rw [h]
  apply tsum_congr
  intro n
  simp only [sourcePiSobolevCoordinates_fst, sourcePiSobolevCoordinates_snd,
    norm_mul, Complex.norm_real]
  rw [Real.norm_of_nonneg ((SpectralWeight.piSobolev k (Nat.cast_nonneg k)).positive (2*n)).le]
  simp only [SpectralWeight.piSobolev_apply, Real.rpow_natCast, mul_pow, ← pow_mul]
  rw [Nat.mul_comm k 2]
  ring

/-- Decoding the exact physical coordinates recovers the original source. -/
theorem normalizedWeightedSource_sourcePiSobolevCoordinates (m k : ℕ) (hk : k ≤ m)
    (a : SobolevSource m) :
    normalizedWeightedSource (SpectralWeight.piSobolev k (Nat.cast_nonneg k))
      (sourcePiSobolevCoordinates m k hk a) = higherSobolevSourceInclusion m a := by
  apply (CoeffPair.toMax 2).injective
  apply Prod.ext <;> ext n
  · change (normalizedWeightedSource _ _).fst n = (higherSobolevSourceInclusion m a).fst n
    rw [normalizedWeightedSource_fst, sourcePiSobolevCoordinates_fst, higherSobolevSourceInclusion_fst]
    exact mul_div_cancel_left₀ _ ((SpectralWeight.piSobolev k (Nat.cast_nonneg k)).toWeight.complex_ne_zero _)
  · change (normalizedWeightedSource _ _).snd n = (higherSobolevSourceInclusion m a).snd n
    rw [normalizedWeightedSource_snd, sourcePiSobolevCoordinates_snd, higherSobolevSourceInclusion_snd]
    exact mul_div_cancel_left₀ _ ((SpectralWeight.piSobolev k (Nat.cast_nonneg k)).toWeight.complex_ne_zero _)

/-- Every source has the exact weighted period-one realization needed by the action estimate. -/
theorem weightedBaseToPair_sourcePiSobolevCoordinates (m k : ℕ) (hk : k ≤ m)
    (a : SobolevSource m) :
    weightedBaseToPair (SpectralWeight.piSobolev k (Nat.cast_nonneg k))
      (normalizedWeightedPeriodOne _ (sourcePiSobolevCoordinates m k hk a)) =
      periodOnePotential (higherSobolevSourceInclusion m a) := by
  rw [weightedBaseToPair_normalizedWeightedPeriodOne,
    normalizedWeightedSource_sourcePiSobolevCoordinates]

end NLS.ZakharovShabat
