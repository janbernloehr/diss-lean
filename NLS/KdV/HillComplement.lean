import NLS.KdV.FreeHill
import NLS.SequenceSpaces.ReciprocalSeries
import NLS.SequenceSpaces.WeightedHolderMultiplier
import NLS.SequenceSpaces.SpectralConvolution
import NLS.FunctionalAnalysis.NeumannCompositionBound

/-!
# Hilbert-to-summable gain for the free Hill complement

This is the sequence-space step of arXiv:1502.04550v1, Lemma A.3 (page 27).
On the explicit radius-`6*n` strips of `FreeHill`, the complementary inverse
maps weighted l2 into weighted l1 with bound `4/n`. Weighted convolution
therefore gives a tail perturbation bound `4*norm(q)/n`.
These statements concern Fourier coefficients; identification with the
periodic differential operator and its spectrum is a separate obligation.
-/

noncomputable section
open scoped ENNReal
namespace NLS.KdV

private theorem reciprocal_sq (k : ℤ) :
    ‖(((|(k : ℝ)|)⁻¹ : ℝ) : ℂ)‖^2 =
      if k = 0 then 0 else |(k : ℝ)| ^ (-(2 : ℝ)) := by
  by_cases hk : k = 0
  · simp [hk]
  · simp only [if_neg hk, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_abs,
      Real.rpow_neg (abs_nonneg (k : ℝ)), Real.rpow_two, inv_pow]

/-- The punctured reciprocal lattice, obtained from the existing series theorem. -/
private def reciprocalLattice : Coeff 2 :=
  ⟨fun k => (((|(k : ℝ)|)⁻¹ : ℝ) : ℂ), by
    change Memℓp (fun k : ℤ => (((|(k : ℝ)|)⁻¹ : ℝ) : ℂ)) 2
    rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, reciprocal_sq, zero_add] using
      (ReciprocalSeries.summable_int_shifted_rpow (α := 0) (q := 2)
        (by norm_num) (by norm_num))⟩

private theorem norm_reciprocalLattice_le : ‖reciprocalLattice‖ ≤ 2 := by
  apply lp.norm_le_of_tsum_le (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (by norm_num)
  have h := ReciprocalSeries.tsum_int_shifted_rpow_le (α := 0) (q := 2)
    (by norm_num) (by norm_num)
  change (∑' k : ℤ, ‖(((|(k : ℝ)|)⁻¹ : ℝ) : ℂ)‖ ^ (2 : ℝ≥0∞).toReal) ≤
    (2 : ℝ) ^ (2 : ℝ≥0∞).toReal
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, reciprocal_sq]
  convert h using 1 <;> norm_num

private def reciprocalEnvelope (n : ℕ) : Coeff 2 :=
  (((n : ℝ)⁻¹ : ℝ) : ℂ) •
    (Coeff.shift (n : ℤ) reciprocalLattice + Coeff.shift (-(n : ℤ)) reciprocalLattice)

private theorem norm_reciprocalEnvelope_apply (n : ℕ) (k : ℤ) :
    ‖reciprocalEnvelope n k‖ =
      (n : ℝ)⁻¹ * (|((k - (n : ℤ) : ℤ) : ℝ)|⁻¹ +
        |((k + (n : ℤ) : ℤ) : ℝ)|⁻¹) := by
  change ‖(((n : ℝ)⁻¹ : ℝ) : ℂ) *
    ((((|((k - (n : ℤ) : ℤ) : ℝ)|)⁻¹ : ℝ) : ℂ) +
      (((|((k - -(n : ℤ) : ℤ) : ℝ)|)⁻¹ : ℝ) : ℂ))‖ = _
  rw [sub_neg_eq_add, ← Complex.ofReal_add, ← Complex.ofReal_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (by positivity)]

private theorem norm_reciprocalEnvelope_le (n : ℕ) :
    ‖reciprocalEnvelope n‖ ≤ 4 / (n : ℝ) := by
  rw [reciprocalEnvelope, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ (n : ℝ)⁻¹)]
  calc
    _ ≤ (n : ℝ)⁻¹ * (‖Coeff.shift (n : ℤ) reciprocalLattice‖ +
        ‖Coeff.shift (-(n : ℤ)) reciprocalLattice‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
    _ ≤ (n : ℝ)⁻¹ * (2+2) := by
      rw [Coeff.norm_shift, Coeff.norm_shift]
      exact mul_le_mul_of_nonneg_left
        (add_le_add norm_reciprocalLattice_le norm_reciprocalLattice_le) (by positivity)
    _ = _ := by ring

private theorem reciprocal_symbol_le_envelope {n : ℕ} (hn : 1 ≤ n) {z : ℂ}
    (hz : z ∈ reducedHillStrip n) (k : ℤ) :
    ‖reducedHillSymbol n hn z hz k‖ ≤ ‖reciprocalEnvelope n k‖ := by
  change ‖if k.natAbs = n then (0 : ℂ) else _‖ ≤ _
  by_cases hk : k.natAbs = n
  · simp only [if_pos hk, norm_zero]; exact norm_nonneg _
  rw [if_neg hk, norm_inv, norm_reciprocalEnvelope_apply]
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hkn : k ≠ (n : ℤ) := by intro h; apply hk; simp [h]
  have hkn' : k ≠ -(n : ℤ) := by intro h; apply hk; simp [h]
  have hden := freeHill_denominator_lower hn hz hk
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
    rw [mul_inv_rev] at hi
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
    rw [mul_inv_rev] at hi
    have hother : 0 ≤ (n : ℝ)⁻¹ * |((k - (n : ℤ) : ℤ) : ℝ)|⁻¹ := by positivity
    nlinarith

/-- Square summability of the actual complementary Hill reciprocal symbol. -/
theorem reducedHillSymbol_memlp_two (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ reducedHillStrip n) : Memℓp (fun k => reducedHillSymbol n hn z hz k) 2 :=
  (lp.memℓp (reciprocalEnvelope n)).mono' (reciprocal_symbol_le_envelope hn hz)

/-- The same reciprocal symbol in the Hilbert space, not just the bounded space. -/
def reducedHillHilbertSymbol (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ reducedHillStrip n) : Coeff 2 :=
  ⟨_, reducedHillSymbol_memlp_two n hn z hz⟩

@[simp] theorem reducedHillHilbertSymbol_apply (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ reducedHillStrip n) (k : ℤ) :
    reducedHillHilbertSymbol n hn z hz k =
      if k.natAbs = n then 0 else (z - (freeHillValue k : ℂ))⁻¹ := rfl

theorem norm_reducedHillHilbertSymbol_le (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ reducedHillStrip n) : ‖reducedHillHilbertSymbol n hn z hz‖ ≤ 4/(n : ℝ) :=
  (lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (reciprocal_symbol_le_envelope hn hz)).trans (norm_reciprocalEnvelope_le n)

/-- The complementary inverse gains the summability required by Young's inequality. -/
def hillComplementToL1 (w : Weight) (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ reducedHillStrip n) : WeightedCoeff w 2 →L[ℂ] WeightedCoeff w 1 :=
  WeightedCoeff.holderMultiplier w (reducedHillHilbertSymbol n hn z hz)

@[simp] theorem hillComplementToL1_apply (w : Weight) (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ reducedHillStrip n) (a : WeightedCoeff w 2) (k : ℤ) :
    (hillComplementToL1 w n hn z hz a).val k =
      if k.natAbs = n then 0 else (z-(freeHillValue k : ℂ))⁻¹*a.val k := by
  rw [hillComplementToL1, WeightedCoeff.holderMultiplier_apply, reducedHillHilbertSymbol_apply]
  split_ifs <;> simp

theorem norm_hillComplementToL1_apply_le (w : Weight) (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ reducedHillStrip n) (a : WeightedCoeff w 2) :
    ‖hillComplementToL1 w n hn z hz a‖ ≤ (4/(n : ℝ))*‖a‖ :=
  (WeightedCoeff.norm_holderMultiplier_le w _ a).trans
    (mul_le_mul_of_nonneg_right (norm_reducedHillHilbertSymbol_le n hn z hz) (norm_nonneg a))

/-- The summability gain is uniform over all shifted weighted norms. -/
theorem shiftedNorm_hillComplementToL1_le (w : SpectralWeight) (i : ℤ)
    (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (a : WeightedCoeff w.toWeight 2) :
    w.shiftedNorm i (hillComplementToL1 w.toWeight n hn z hz a) ≤
      (4/(n : ℝ))*w.shiftedNorm i a :=
  (WeightedCoeff.shiftedNorm_holderMultiplier_le w i _ a).trans
    (mul_le_mul_of_nonneg_right (norm_reducedHillHilbertSymbol_le n hn z hz) (norm_nonneg _))

/-- Fourier realization of `V*A_lambda^-1*Q_n` for a period-two potential. -/
def hillTailPerturbation (w : SpectralWeight) (q : WeightedCoeff w.toWeight 2)
    (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ∈ reducedHillStrip n) :
    WeightedCoeff w.toWeight 2 →L[ℂ] WeightedCoeff w.toWeight 2 :=
  (w.convolutionCLM q).comp (hillComplementToL1 w.toWeight n hn z hz)

/-- The literal convolution formula for the Fourier tail operator. -/
theorem hillTailPerturbation_apply (w : SpectralWeight) (q : WeightedCoeff w.toWeight 2)
    (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (a : WeightedCoeff w.toWeight 2) (k : ℤ) :
    (hillTailPerturbation w q n hn z hz a).val k =
      ∑' j : ℤ, q.val (k-j) *
        (if j.natAbs = n then 0 else (z-(freeHillValue j : ℂ))⁻¹*a.val j) := by
  simp only [hillTailPerturbation, ContinuousLinearMap.comp_apply,
    SpectralWeight.convolutionCLM_apply, SpectralWeight.convolution_apply,
    hillComplementToL1_apply]

theorem norm_hillTailPerturbation_apply_le (w : SpectralWeight)
    (q : WeightedCoeff w.toWeight 2) (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ reducedHillStrip n) (a : WeightedCoeff w.toWeight 2) :
    ‖hillTailPerturbation w q n hn z hz a‖ ≤ (4*‖q‖/(n : ℝ))*‖a‖ := by
  apply (w.norm_convolution_le q _).trans
  calc
    ‖q‖ * ‖hillComplementToL1 w.toWeight n hn z hz a‖ ≤
        ‖q‖ * ((4/(n : ℝ))*‖a‖) :=
      mul_le_mul_of_nonneg_left (norm_hillComplementToL1_apply_le _ n hn z hz a) (norm_nonneg q)
    _ = _ := by ring

theorem norm_hillTailPerturbation_le (w : SpectralWeight)
    (q : WeightedCoeff w.toWeight 2) (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ reducedHillStrip n) :
    ‖hillTailPerturbation w q n hn z hz‖ ≤ 4*‖q‖/(n : ℝ) :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    (norm_hillTailPerturbation_apply_le w q n hn z hz)

/-- Lemma A.3's shifted-norm form, with the explicit constant `4` and strip `6*n`. -/
theorem shiftedNorm_hillTailPerturbation_le (w : SpectralWeight) (i : ℤ)
    (q : WeightedCoeff w.toWeight 2) (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ reducedHillStrip n) (a : WeightedCoeff w.toWeight 2) :
    w.shiftedNorm i (hillTailPerturbation w q n hn z hz a) ≤
      (4*‖q‖/(n : ℝ))*w.shiftedNorm i a := by
  apply (w.shiftedNorm_convolution_le i q _).trans
  calc
    ‖q‖ * w.shiftedNorm i (hillComplementToL1 w.toWeight n hn z hz a) ≤
        ‖q‖ * ((4/(n : ℝ))*w.shiftedNorm i a) :=
      mul_le_mul_of_nonneg_left (shiftedNorm_hillComplementToL1_le w i n hn z hz a)
        (norm_nonneg q)
    _ = _ := by ring

/-- The Fourier tail is a half-contraction above an explicit norm threshold. -/
theorem norm_hillTailPerturbation_le_half (w : SpectralWeight)
    (q : WeightedCoeff w.toWeight 2) (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ reducedHillStrip n) (hcut : 8*‖q‖ ≤ (n : ℝ)) :
    ‖hillTailPerturbation w q n hn z hz‖ ≤ (1/2 : ℝ) := by
  apply (norm_hillTailPerturbation_le w q n hn z hz).trans
  apply (div_le_iff₀ (show (0 : ℝ) < n by exact_mod_cast (show 0 < n by omega))).mpr
  linarith

/-- A genuine two-sided inverse with norm at most two, using the library's
Neumann construction after the proved Hill perturbation estimate. -/
theorem exists_hillTailCorrection (w : SpectralWeight)
    (q : WeightedCoeff w.toWeight 2) (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ reducedHillStrip n) (hcut : 8*‖q‖ ≤ (n : ℝ)) :
    ∃ R : WeightedCoeff w.toWeight 2 →L[ℂ] WeightedCoeff w.toWeight 2,
      (ContinuousLinearMap.id ℂ _ - hillTailPerturbation w q n hn z hz).comp R =
        ContinuousLinearMap.id ℂ _ ∧
      R.comp (ContinuousLinearMap.id ℂ _ - hillTailPerturbation w q n hn z hz) =
        ContinuousLinearMap.id ℂ _ ∧ ‖R‖ ≤ 2 := by
  let K := hillTailPerturbation w q n hn z hz
  let Id := ContinuousLinearMap.id ℂ (WeightedCoeff w.toWeight 2)
  have hnear : ‖Id.comp (Id - (Id-K))‖ ≤ (1/2 : ℝ) := by
    simpa [Id] using norm_hillTailPerturbation_le_half w q n hn z hz hcut
  obtain ⟨R, hleft, hright, hnorm⟩ :=
    NLS.exists_inverse_norm_le_two_mul_of_composition_near (Id-K) Id Id
      (by simp [Id]) (by simp [Id]) hnear
  refine ⟨R, hleft, hright, hnorm.trans ?_⟩
  have hid : ‖Id‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  linarith

end NLS.KdV
