import NLS.KdV.HillComplement

/-! Sharper complementary estimates on the checked radius-6*n strips.
The printed radius-12*n convention is handled separately in the article audit. -/

noncomputable section
set_option autoImplicit false
open scoped ENNReal
namespace NLS.KdV
namespace SharpComplement

private theorem sharpReciprocal_sq (k : ℤ) :
    ‖(((|(k : ℝ)|)⁻¹ : ℝ) : ℂ)‖^2 =
      if k = 0 then 0 else |(k : ℝ)| ^ (-(2 : ℝ)) := by
  by_cases hk : k = 0
  · simp [hk]
  · simp only [if_neg hk, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_abs,
      Real.rpow_neg (abs_nonneg (k : ℝ)), Real.rpow_two, inv_pow]

/-- The punctured reciprocal lattice, obtained from the existing series theorem. -/
private def sharpReciprocalLattice : Coeff 2 :=
  ⟨fun k => (((|(k : ℝ)|)⁻¹ : ℝ) : ℂ), by
    change Memℓp (fun k : ℤ => (((|(k : ℝ)|)⁻¹ : ℝ) : ℂ)) 2
    rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, sharpReciprocal_sq, zero_add] using
      (ReciprocalSeries.summable_int_shifted_rpow (α := 0) (q := 2)
        (by norm_num) (by norm_num))⟩

private theorem norm_sharpReciprocalLattice_le : ‖sharpReciprocalLattice‖ ≤ 2 := by
  apply lp.norm_le_of_tsum_le (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (by norm_num)
  have h := ReciprocalSeries.tsum_int_shifted_rpow_le (α := 0) (q := 2)
    (by norm_num) (by norm_num)
  change (∑' k : ℤ, ‖(((|(k : ℝ)|)⁻¹ : ℝ) : ℂ)‖ ^ (2 : ℝ≥0∞).toReal) ≤
    (2 : ℝ) ^ (2 : ℝ≥0∞).toReal
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, sharpReciprocal_sq]
  convert h using 1 <;> norm_num

private def sharpReciprocalEnvelope (n : ℕ) : Coeff 2 :=
  (((n : ℝ)⁻¹ : ℝ) : ℂ) •
    (Coeff.shift (n : ℤ) sharpReciprocalLattice + Coeff.shift (-(n : ℤ)) sharpReciprocalLattice)

private theorem norm_sharpReciprocalEnvelope_apply (n : ℕ) (k : ℤ) :
    ‖sharpReciprocalEnvelope n k‖ =
      (n : ℝ)⁻¹ * (|((k - (n : ℤ) : ℤ) : ℝ)|⁻¹ +
        |((k + (n : ℤ) : ℤ) : ℝ)|⁻¹) := by
  change ‖(((n : ℝ)⁻¹ : ℝ) : ℂ) *
    ((((|((k - (n : ℤ) : ℤ) : ℝ)|)⁻¹ : ℝ) : ℂ) +
      (((|((k - -(n : ℤ) : ℤ) : ℝ)|)⁻¹ : ℝ) : ℂ))‖ = _
  rw [sub_neg_eq_add, ← Complex.ofReal_add, ← Complex.ofReal_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (by positivity)]

private theorem norm_sharpReciprocalEnvelope_le (n : ℕ) :
    ‖sharpReciprocalEnvelope n‖ ≤ 4 / (n : ℝ) := by
  rw [sharpReciprocalEnvelope, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ (n : ℝ)⁻¹)]
  calc
    _ ≤ (n : ℝ)⁻¹ * (‖Coeff.shift (n : ℤ) sharpReciprocalLattice‖ +
        ‖Coeff.shift (-(n : ℤ)) sharpReciprocalLattice‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
    _ ≤ (n : ℝ)⁻¹ * (2+2) := by
      rw [Coeff.norm_shift, Coeff.norm_shift]
      exact mul_le_mul_of_nonneg_left
        (add_le_add norm_sharpReciprocalLattice_le norm_sharpReciprocalLattice_le) (by positivity)
    _ = _ := by ring

private theorem reciprocal_symbol_le_envelope_of_lower {n : ℕ} (hn : 1 ≤ n) (z : ℂ)
    (hdenom : ∀ k : ℤ, k.natAbs ≠ n → |(n : ℝ)^2-(k : ℝ)^2| ≤
      ‖z-(freeHillValue k : ℂ)‖/2) (k : ℤ) :
    2 * ‖if k.natAbs = n then (0 : ℂ) else (z-(freeHillValue k : ℂ))⁻¹‖ ≤
      ‖sharpReciprocalEnvelope n k‖ := by
  by_cases hk : k.natAbs = n
  · simp only [if_pos hk, norm_zero, mul_zero]; exact norm_nonneg _
  rw [if_neg hk, norm_inv, norm_sharpReciprocalEnvelope_apply]
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hkn : k ≠ (n : ℤ) := by intro h; apply hk; simp [h]
  have hkn' : k ≠ -(n : ℤ) := by intro h; apply hk; simp [h]
  have hden := hdenom k hk
  by_cases hkpos : 0 ≤ k
  · have hkpos' : (0 : ℝ) ≤ k := by exact_mod_cast hkpos
    have hdpos : 0 < |((k - (n : ℤ) : ℤ) : ℝ)| := by
      exact abs_pos.mpr (by exact_mod_cast (sub_ne_zero.mpr hkn))
    have hfactor : (n : ℝ)*|((k - (n : ℤ) : ℤ) : ℝ)| ≤
        |(n : ℝ)^2 - (k : ℝ)^2| := by
      simp only [Int.cast_sub, Int.cast_natCast]
      rw [show (n : ℝ)^2-(k : ℝ)^2 = ((n : ℝ)+(k : ℝ))*((n : ℝ)-(k : ℝ)) by ring,
        abs_mul, abs_of_nonneg (show 0 ≤ (n : ℝ)+(k : ℝ) by positivity), abs_sub_comm]
      nlinarith [mul_nonneg hkpos' (abs_nonneg ((n : ℝ)-(k : ℝ)))]
    have hi := inv_anti₀ (mul_pos hnpos hdpos) (hfactor.trans hden)
    rw [inv_div, div_eq_mul_inv, mul_inv_rev] at hi
    have hother : 0 ≤ (n : ℝ)⁻¹ * |((k + (n : ℤ) : ℤ) : ℝ)|⁻¹ := by positivity
    nlinarith

  · have hkneg : (k : ℝ) ≤ 0 := by exact_mod_cast (show k ≤ 0 by omega)
    have hdpos : 0 < |((k + (n : ℤ) : ℤ) : ℝ)| := by
      exact abs_pos.mpr (by exact_mod_cast (show k + (n : ℤ) ≠ 0 by omega))
    have hfactor : (n : ℝ)*|((k + (n : ℤ) : ℤ) : ℝ)| ≤
        |(n : ℝ)^2 - (k : ℝ)^2| := by
      simp only [Int.cast_add, Int.cast_natCast]
      rw [show (n : ℝ)^2-(k : ℝ)^2 = ((n : ℝ)-(k : ℝ))*((k : ℝ)+(n : ℝ)) by ring,
        abs_mul, abs_of_nonneg (show 0 ≤ (n : ℝ)-(k : ℝ) by linarith)]
      nlinarith [mul_nonneg (neg_nonneg.mpr hkneg) (abs_nonneg ((k : ℝ)+(n : ℝ)))]
    have hi := inv_anti₀ (mul_pos hnpos hdpos) (hfactor.trans hden)
    rw [inv_div, div_eq_mul_inv, mul_inv_rev] at hi
    have hother : 0 ≤ (n : ℝ)⁻¹ * |((k - (n : ℤ) : ℤ) : ℝ)|⁻¹ := by positivity
    nlinarith


end SharpComplement

/-- The smaller strip retains enough free energy separation for the sharp
constant two in the tail estimate, including n=1. -/
theorem freeHill_denominator_lower_twice {n : ℕ} (hn : 1 ≤ n) {z : ℂ}
    (hz : z ∈ reducedHillStrip n) {k : ℤ} (hk : k.natAbs ≠ n) :
    2*|(n : ℝ)^2-(k : ℝ)^2| ≤ ‖z-(freeHillValue k : ℂ)‖ := by
  let d : ℝ := |(n : ℝ)^2-(k : ℝ)^2|
  have hnd : (n : ℝ) ≤ d := nat_le_abs_sq_sub_sq hn hk
  have hpi : 9 < Real.pi^2 := by nlinarith [Real.pi_gt_three]
  have he : Real.pi^2*d = |freeHillValue n-freeHillValue k| := by
    dsimp [d,freeHillValue]
    simp only [Int.cast_natCast]
    rw [← mul_sub,abs_mul,abs_of_nonneg (sq_nonneg Real.pi)]
  have ht : Real.pi^2*d ≤ 6*(n : ℝ)+‖z-(freeHillValue k : ℂ)‖ := by
    rw [he]
    calc
      _ ≤ |freeHillValue n-z.re|+|z.re-freeHillValue k| := by
        simpa using abs_add_le (freeHillValue n-z.re) (z.re-freeHillValue k)
      _ ≤ _ := add_le_add
        (by simpa only [reducedHillStrip,Set.mem_ofPred_eq,abs_sub_comm] using hz)
        (by simpa using Complex.abs_re_le_norm (z-(freeHillValue k : ℂ)))
  have hd : 0 ≤ d := abs_nonneg _
  change 2*d ≤ _
  nlinarith

theorem norm_reducedHillHilbertSymbol_le_two (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ reducedHillStrip n) :
    ‖reducedHillHilbertSymbol n hn z hz‖ ≤ 2/(n : ℝ) := by
  have hp (k : ℤ) :
      ‖((2 : ℂ) • reducedHillHilbertSymbol n hn z hz) k‖ ≤
        ‖SharpComplement.sharpReciprocalEnvelope n k‖ := by
    simpa only [lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,norm_mul,
      Complex.norm_ofNat,reducedHillHilbertSymbol_apply] using
      SharpComplement.reciprocal_symbol_le_envelope_of_lower hn z
        (fun k hk => by linarith [freeHill_denominator_lower_twice hn hz hk]) k
  have h := (lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0) hp).trans
    (SharpComplement.norm_sharpReciprocalEnvelope_le n)
  rw [norm_smul,Complex.norm_ofNat] at h
  have he : 4/(n : ℝ) = 2*(2/(n : ℝ)) := by ring
  rw [he] at h
  linarith

theorem shiftedNorm_hillTailPerturbation_le_two (w : SpectralWeight) (i : ℤ)
    (q : WeightedCoeff w.toWeight 2) (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ reducedHillStrip n) (a : WeightedCoeff w.toWeight 2) :
    w.shiftedNorm i (hillTailPerturbation w q n hn z hz a) ≤
      (2*‖q‖/(n : ℝ))*w.shiftedNorm i a := by
  apply (w.shiftedNorm_convolution_le i q _).trans
  have h := (WeightedCoeff.shiftedNorm_holderMultiplier_le w i
    (reducedHillHilbertSymbol n hn z hz) a).trans
      (mul_le_mul_of_nonneg_right (norm_reducedHillHilbertSymbol_le_two n hn z hz)
        (norm_nonneg _))
  change w.shiftedNorm i (hillComplementToL1 w.toWeight n hn z hz a) ≤ _ at h
  calc
    _ ≤ ‖q‖*((2/(n : ℝ))*w.shiftedNorm i a) :=
      mul_le_mul_of_nonneg_left h (norm_nonneg q)
    _ = _ := by ring
theorem norm_hillTailPerturbation_le_two (w : SpectralWeight)
    (q : WeightedCoeff w.toWeight 2) (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ reducedHillStrip n) :
    ‖hillTailPerturbation w q n hn z hz‖ ≤ 2*‖q‖/(n : ℝ) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro a
  simpa only [SpectralWeight.shiftedNorm_zero] using
    shiftedNorm_hillTailPerturbation_le_two w 0 q n hn z hz a

/-- The Fourier tail is a half-contraction above an explicit norm threshold. -/
theorem norm_hillTailPerturbation_le_half_four (w : SpectralWeight)
    (q : WeightedCoeff w.toWeight 2) (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ reducedHillStrip n) (hcut : 4*‖q‖ ≤ (n : ℝ)) :
    ‖hillTailPerturbation w q n hn z hz‖ ≤ (1/2 : ℝ) := by
  apply (norm_hillTailPerturbation_le_two w q n hn z hz).trans
  apply (div_le_iff₀ (show (0 : ℝ) < n by exact_mod_cast (show 0 < n by omega))).mpr
  linarith

/-- A genuine two-sided inverse with norm at most two, using the library's
Neumann construction after the proved Hill perturbation estimate. -/
theorem exists_hillTailCorrection_four (w : SpectralWeight)
    (q : WeightedCoeff w.toWeight 2) (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ reducedHillStrip n) (hcut : 4*‖q‖ ≤ (n : ℝ)) :
    ∃ R : WeightedCoeff w.toWeight 2 →L[ℂ] WeightedCoeff w.toWeight 2,
      (ContinuousLinearMap.id ℂ _ - hillTailPerturbation w q n hn z hz).comp R =
        ContinuousLinearMap.id ℂ _ ∧
      R.comp (ContinuousLinearMap.id ℂ _ - hillTailPerturbation w q n hn z hz) =
        ContinuousLinearMap.id ℂ _ ∧ ‖R‖ ≤ 2 := by
  let K := hillTailPerturbation w q n hn z hz
  let Id := ContinuousLinearMap.id ℂ (WeightedCoeff w.toWeight 2)
  have hnear : ‖Id.comp (Id - (Id-K))‖ ≤ (1/2 : ℝ) := by
    simpa [Id] using norm_hillTailPerturbation_le_half_four w q n hn z hz hcut
  obtain ⟨R, hleft, hright, hnorm⟩ :=
    NLS.exists_inverse_norm_le_two_mul_of_composition_near (Id-K) Id Id
      (by simp [Id]) (by simp [Id]) hnear
  refine ⟨R, hleft, hright, hnorm.trans ?_⟩
  have hid : ‖Id‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  linarith

end NLS.KdV
