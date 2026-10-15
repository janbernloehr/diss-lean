import NLS.ZakharovShabat.SobolevSourceFourierModes
import NLS.Fourier.PeriodOneSobolev
import NLS.SequenceSpaces.ConjugateReflection

/-! # Finite Fourier sums in the original Sobolev spaces

Finite sums retain exact weighted norms and physical derivative values.
Conjugate reflection completes any scalar source to a real source pair.
-/
noncomputable section
open scoped BigOperators ENNReal
open NLS.Fourier
namespace NLS.ZakharovShabat

/-- A finite sum of raw Fourier modes at any integer Sobolev order. -/
def sobolevSourceFourierSum (m : ℕ) (S : Finset ℤ) (c : ℤ → ℝ) : ScalarSobolev m :=
  ∑ n ∈ S, sobolevSourceScalarMode m n (c n)

/-- The physical weighted coordinates are the literal finite single-coefficient sum. -/
theorem sobolevSourceFourierSum_pi (m k : ℕ) (hk : k ≤ m) (S : Finset ℤ) (c : ℤ → ℝ) :
    sourcePiSobolevScalar m k hk (sobolevSourceFourierSum m S c) =
      ∑ n ∈ S, lp.single 2 n (((1+2*Real.pi*|(n:ℝ)|)^k*c n:ℝ):ℂ) := by
  classical
  induction S using Finset.induction_on with
  | empty => ext j; simp [sobolevSourceFourierSum]
  | @insert n S hn ih =>
    have hadd (a b : ScalarSobolev m) : sourcePiSobolevScalar m k hk (a+b) =
        sourcePiSobolevScalar m k hk a+sourcePiSobolevScalar m k hk b := by
      ext j; simp [WeightedCoeff.add_val,mul_add]
    simp only [sobolevSourceFourierSum,Finset.sum_insert hn] at *
    rw [hadd,ih,sobolevSourceScalarMode_piCoordinates]

/-- Exact weighted energy of a finite Fourier sum, including signed frequencies. -/
theorem sobolevSourceFourierSum_pi_sq (m k : ℕ) (hk : k ≤ m) (S : Finset ℤ) (c : ℤ → ℝ) :
    ‖sourcePiSobolevScalar m k hk (sobolevSourceFourierSum m S c)‖^2 =
      ∑ n ∈ S, ((1+2*Real.pi*|(n:ℝ)|)^k*c n)^2 := by
  rw [sobolevSourceFourierSum_pi]
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two,Complex.norm_real,Real.norm_eq_abs,sq_abs] using
    lp.norm_sum_single (p := 2) (by norm_num)
      (fun n : ℤ => (((1+2*Real.pi*|(n:ℝ)|)^k*c n:ℝ):ℂ)) S

/-- Forgetting regularity retains all finite raw Fourier coefficients. -/
theorem sobolevSourceFourierSum_L2 (m : ℕ) (S : Finset ℤ) (c : ℤ → ℝ) :
    WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) (sobolevSourceFourierSum m S c) =
      ∑ n ∈ S, lp.single 2 n (c n:ℂ) := by
  simp only [sobolevSourceFourierSum,map_sum,sobolevSourceScalarMode_L2]

/-- Raw coefficients retain exactly the finite support, including its boundary indices. -/
theorem sobolevSourceFourierSum_apply (m : ℕ) (S : Finset ℤ) (c : ℤ → ℝ) (j : ℤ) :
    (sobolevSourceFourierSum m S c).val j = if j ∈ S then (c j:ℂ) else 0 := by
  classical
  rw [← WeightedCoeff.sobolevToL2_apply (Nat.cast_nonneg m) (sobolevSourceFourierSum m S c) j,
    sobolevSourceFourierSum_L2]
  simp only [lp.coeFn_sum,Finset.sum_apply,lp.coeFn_single,Finset.sum_pi_single]

/-- The first physical derivative of one mode at the origin has its exact 2π multiplier. -/
theorem sobolevSourceScalarMode_firstJet_zero (n : ℤ) (c : ℝ) :
    hierarchySobolevJetContinuous 2 1 (by omega) (sobolevSourceScalarMode 2 n c) 0 =
      2*Complex.I*(Real.pi:ℂ)*n*c := by
  have he : hierarchySobolevToScalarDomain 1 le_rfl
      (hierarchySobolevJet 2 1 (by omega) (sobolevSourceScalarMode 2 n c)) =
        scalarMode n (2*Complex.I*(Real.pi:ℂ)*n*c) := by
    apply Subtype.ext
    funext j
    simp only [hierarchySobolevToScalarDomain_apply,hierarchySobolevJet_apply,
      sobolevSourceScalarMode_apply,scalarMode_apply,pow_one]
    by_cases h : j = n
    · subst j; simp
    · simp [h]
  change periodOneSobolevSynthesis
    (hierarchySobolevToScalarDomain 1 le_rfl
      (hierarchySobolevJet 2 1 (by omega) (sobolevSourceScalarMode 2 n c))) (0:AddCircle (2:ℝ)) = _
  rw [he]
  simpa [wave] using periodOneSobolevSynthesis_scalarMode n (2*Complex.I*(Real.pi:ℂ)*n*c) 0

/-- The physical first derivative at zero is the finite sum of the exact Fourier multipliers. -/
theorem sobolevSourceFourierSum_jet_zero (S : Finset ℤ) (c : ℤ → ℝ) :
    hierarchySobolevJetContinuous 2 1 (by omega) (sobolevSourceFourierSum 2 S c) 0 =
      ∑ n ∈ S, 2*Complex.I*(Real.pi:ℂ)*n*c n := by
  simp only [sobolevSourceFourierSum,map_sum,ContinuousMap.sum_apply,sobolevSourceScalarMode_firstJet_zero]

/-- Pair a scalar source with its physical conjugate to obtain a real original source. -/
def sobolevSourceRealCompletion (m : ℕ) (a : ScalarSobolev m) : realTypeHigherSobolevSourceLocus m :=
  ⟨(a,WeightedCoeff.conjugateReflection (Weight.sobolev m) (by intro n; simp) a),by
    intro n
    change (higherSobolevSourceInclusion m _).snd n =
      (starRingEnd ℂ) ((higherSobolevSourceInclusion m _).fst (-n))
    simp only [higherSobolevSourceInclusion_snd,higherSobolevSourceInclusion_fst,
      WeightedCoeff.conjugateReflection_apply]⟩

end NLS.ZakharovShabat
