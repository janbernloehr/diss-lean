import NLS.ZakharovShabat.SourceBoundarySeries
import NLS.ZakharovShabat.SourcePiSobolevCoordinates
import NLS.ZakharovShabat.SourceHigherSobolevFiniteGapDensity

/-! # Real Fourier modes in the original Sobolev source

Single signed modes retain exact physical jet and weighted Hilbert norms.
The two components are related by complex conjugation and reflection.
-/
noncomputable section
open scoped ComplexConjugate
namespace NLS.ZakharovShabat

/-- A raw Fourier mode with real amplitude at any integer Sobolev order. -/
def sobolevSourceScalarMode (m : ℕ) (n : ℤ) (c : ℝ) : ScalarSobolev m :=
  (c:ℂ) • sourceWeightedSingle m n

/-- The mode has exactly one nonzero raw coefficient. -/
theorem sobolevSourceScalarMode_apply (m : ℕ) (n k : ℤ) (c : ℝ) :
    (sobolevSourceScalarMode m n c).val k = if k = n then (c:ℂ) else 0 := by
  change (c:ℂ)*(sourceWeightedSingle (p := 2) m n).val k = _
  rw [sourceWeightedSingle_apply]
  split_ifs <;> simp

/-- The conjugate-reflected pair is an actual real original Sobolev source. -/
def sobolevSourceRealMode (m : ℕ) (n : ℤ) (c : ℝ) : realTypeHigherSobolevSourceLocus m :=
  ⟨(sobolevSourceScalarMode m n c, sobolevSourceScalarMode m (-n) c), by
    intro k
    change (higherSobolevSourceInclusion m _).snd k =
      conj ((higherSobolevSourceInclusion m _).fst (-k))
    simp only [higherSobolevSourceInclusion_snd, higherSobolevSourceInclusion_fst,
      sobolevSourceScalarMode_apply, neg_eq_iff_eq_neg]
    split_ifs <;> simp⟩

/-- Forgetting regularity retains the original single Fourier coefficient. -/
theorem sobolevSourceScalarMode_L2 (m : ℕ) (n : ℤ) (c : ℝ) :
    WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) (sobolevSourceScalarMode m n c) =
      lp.single 2 n (c:ℂ) := by
  ext k
  simp [WeightedCoeff.sobolevToL2_apply, sobolevSourceScalarMode_apply,
    lp.single_apply, Pi.single_apply, eq_comm]

/-- Every physical derivative has the exact period-one multiplier. -/
theorem sobolevSourceScalarMode_jet (m k : ℕ) (hk : k ≤ m) (n : ℤ) (c : ℝ) :
    hierarchySobolevJetL2 m k hk (sobolevSourceScalarMode m n c) =
      lp.single 2 n ((2*Complex.I*(Real.pi:ℂ)*n)^k*(c:ℂ)) := by
  ext j
  simp only [hierarchySobolevJetL2_apply, sobolevSourceScalarMode_apply, lp.single_apply,
    Pi.single_apply]
  by_cases h : j = n
  · subst j; simp
  · simp [h]

/-- The scalar physical L² norm is the absolute amplitude. -/
theorem norm_sobolevSourceScalarMode_L2 (m : ℕ) (n : ℤ) (c : ℝ) :
    ‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) (sobolevSourceScalarMode m n c)‖ = |c| := by
  rw [sobolevSourceScalarMode_L2, lp.norm_single (by norm_num)]
  simp

/-- Exact physical derivative norm, including zero and negative modes. -/
theorem norm_sobolevSourceScalarMode_jet (m k : ℕ) (hk : k ≤ m) (n : ℤ) (c : ℝ) :
    ‖hierarchySobolevJetL2 m k hk (sobolevSourceScalarMode m n c)‖ =
      (2*Real.pi)^k*|(n:ℝ)|^k*|c| := by
  rw [sobolevSourceScalarMode_jet, lp.norm_single (by norm_num), norm_periodOneJetMultiplier]
  simp

/-- Exact physical weighted coordinates of one mode. -/
theorem sobolevSourceScalarMode_piCoordinates (m k : ℕ) (hk : k ≤ m) (n : ℤ) (c : ℝ) :
    sourcePiSobolevScalar m k hk (sobolevSourceScalarMode m n c) =
      lp.single 2 n (((1+2*Real.pi*|(n:ℝ)|)^k*c:ℝ):ℂ) := by
  ext j
  simp only [sourcePiSobolevScalar_apply, sobolevSourceScalarMode_apply, lp.single_apply,
    Pi.single_apply]
  by_cases h : j = n
  · subst j
    simp [SpectralWeight.piSobolev_apply, abs_mul, Real.rpow_natCast,
      abs_of_pos Real.pi_pos, mul_comm, mul_left_comm]
  · simp [h]

/-- The physical weighted norm retains the factor 2π. -/
theorem norm_sobolevSourceScalarMode_piCoordinates (m k : ℕ) (hk : k ≤ m) (n : ℤ) (c : ℝ) :
    ‖sourcePiSobolevScalar m k hk (sobolevSourceScalarMode m n c)‖ =
      (1+2*Real.pi*|(n:ℝ)|)^k*|c| := by
  rw [sobolevSourceScalarMode_piCoordinates, lp.norm_single (by norm_num), Complex.norm_real,
    Real.norm_eq_abs, abs_mul, abs_of_nonneg (show 0 ≤ (1+2*Real.pi*|(n:ℝ)|)^k by positivity)]

/-- The squared pair L² norm includes both conjugate components. -/
theorem sobolevSourceRealMode_mass (m : ℕ) (n : ℤ) (c : ℝ) :
    ‖higherSobolevSourceInclusion m (sobolevSourceRealMode m n c).val‖^2 = 2*c^2 := by
  have he : higherSobolevSourceInclusion m (sobolevSourceRealMode m n c).val =
      WithLp.toLp 2 (lp.single 2 n (c:ℂ), lp.single 2 (-n) (c:ℂ)) := by
    apply (CoeffPair.toMax 2).injective
    apply Prod.ext <;> ext j <;>
      simp [sobolevSourceRealMode, higherSobolevSourceInclusion_fst,
        higherSobolevSourceInclusion_snd, sobolevSourceScalarMode_apply,
        lp.single_apply, Pi.single_apply, eq_comm]
  rw [he, WithLp.prod_norm_sq_eq_of_L2]
  change ‖(lp.single 2 n (c:ℂ) : Coeff 2)‖^2 +
    ‖(lp.single 2 (-n) (c:ℂ) : Coeff 2)‖^2 = _
  simp only [lp.norm_single (by norm_num : (0:ENNReal) < 2),
    Complex.norm_real, Real.norm_eq_abs, sq_abs]
  ring

/-- Exact physical Sobolev pair norm at every lower order. -/
theorem sobolevSourceRealMode_piNorm (m k : ℕ) (hk : k ≤ m) (n : ℤ) (c : ℝ) :
    ‖sourcePiSobolevCoordinates m k hk (sobolevSourceRealMode m n c).val‖^2 =
      2*((1+2*Real.pi*|(n:ℝ)|)^k*|c|)^2 := by
  rw [sourcePiSobolevCoordinates, WithLp.prod_norm_sq_eq_of_L2]
  change ‖sourcePiSobolevScalar m k hk (sobolevSourceScalarMode m n c)‖^2 +
    ‖sourcePiSobolevScalar m k hk (sobolevSourceScalarMode m (-n) c)‖^2 = _
  rw [norm_sobolevSourceScalarMode_piCoordinates, norm_sobolevSourceScalarMode_piCoordinates]
  simp only [Int.cast_neg, abs_neg]
  ring

end NLS.ZakharovShabat
