import NLS.ZakharovShabat.SourceLemma34Holder
import NLS.SequenceSpaces.SobolevConstant

/-! # Explicit corrected radius bounds for the literal Lemma 3.4 subsums -/

noncomputable section
open scoped ENNReal
open Classical
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
local instance : Fact (1 ≤ p.conjExponent) :=
  ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩

/-- The exact scalar reciprocal in the printed proof, in the conjugate space. -/
def lemma34Reciprocal (hp : p ≠ ⊤) (n : ℤ) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    Coeff p.conjExponent :=
  ⟨_, sourceLemma34_reciprocal_memlp hp n hr hr1⟩

theorem lemma34Reciprocal_norm_apply (hp : p ≠ ⊤) (n k : ℤ) {r : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) :
    ‖lemma34Reciprocal hp n hr hr1 k‖ = (r + |((n-k : ℤ) : ℝ)|)⁻¹ := by
  change ‖((r + |((n-k : ℤ) : ℝ)| : ℝ) : ℂ)⁻¹‖ = _
  simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < r + |((n-k : ℤ) : ℝ)|)]

/-- The scalar reciprocal retains its inverse-radius factor, including at p=1. -/
theorem norm_lemma34Reciprocal_le (hp : p ≠ ⊤) (n : ℤ) {r : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) :
    ‖lemma34Reciprocal hp n hr hr1‖ ≤ 2 * p.toReal / r := by
  let b : Coeff p.conjExponent := WeightedCoeff.inverseWeight (Weight.sobolev 1)
    (Weight.inverse_sobolev_one_memlp
      ((ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top))
  have hnorm (k : ℤ) : ‖b k‖ = (1 + |(k : ℝ)|)⁻¹ := by
    change ‖(Weight.sobolev 1 k : ℂ)⁻¹‖ = _
    simp only [Weight.sobolev_apply, Real.rpow_one, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 + |(k : ℝ)|)]
  have hcmp : ‖Coeff.reindex (Equiv.addRight n) (lemma34Reciprocal hp n hr hr1)‖ ≤
      ‖(r : ℂ)⁻¹ • b‖ := by
    apply lp.norm_mono (ne_of_gt (zero_lt_one.trans_le
      (ENNReal.HolderConjugate.one_le p.conjExponent p)))
    intro k
    change ‖lemma34Reciprocal hp n hr hr1 (k+n)‖ ≤ ‖(r : ℂ)⁻¹ * b k‖
    rw [lemma34Reciprocal_norm_apply, norm_mul, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hr, hnorm, ← mul_inv]
    rw [show n - (k + n) = -k by omega, Int.cast_neg, abs_neg]
    apply inv_anti₀ (by positivity)
    nlinarith [mul_le_mul_of_nonneg_right hr1 (abs_nonneg (k : ℝ))]
  rw [Coeff.norm_reindex, norm_smul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hr] at hcmp
  calc
    _ ≤ r⁻¹ * ‖b‖ := hcmp
    _ ≤ r⁻¹ * (2 * p.toReal) := mul_le_mul_of_nonneg_left
      (WeightedCoeff.norm_inverse_sobolev_le hp _) (inv_nonneg.mpr hr.le)
    _ = _ := by ring

/-- The additive-index absolute sandwich has the original scalar norm product bound. -/
theorem lemma34_weighted_sum_le (a b : Coeff p.conjExponent) (φ f : Coeff p) :
    (∑' lm : ℤ × ℤ, ‖a lm.1‖ * (‖φ (lm.1+lm.2)‖ * (‖b lm.2‖ * ‖f lm.2‖))) ≤
      (‖a‖ * ‖b‖) * (‖φ‖ * ‖f‖) := by
  let e := Equiv.prodCongr (Equiv.refl ℤ) (Equiv.neg ℤ)
  have he := e.tsum_eq (fun jk : ℤ × ℤ => ‖a jk.1‖ *
    (‖φ (jk.1-jk.2)‖ * (‖Coeff.reindex (Equiv.neg ℤ) b jk.2‖ *
      ‖Coeff.reindex (Equiv.neg ℤ) f jk.2‖)))
  have hs := Coeff.tsum_sandwich_terms a φ (Coeff.reindex (Equiv.neg ℤ) b)
    (Coeff.reindex (Equiv.neg ℤ) f)
  have hb := Coeff.norm_magnitude_sandwich_le a φ (Coeff.reindex (Equiv.neg ℤ) b)
    (Coeff.reindex (Equiv.neg ℤ) f)
  rw [← hs, ← he] at hb
  simpa only [e, Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply, Equiv.neg_apply,
    Coeff.reindex_apply, neg_neg, sub_neg_eq_add, Coeff.norm_reindex, mul_assoc, mul_comm,
    mul_left_comm] using hb

/-- The entire literal proof sum has an explicit inverse-square radius bound. -/
theorem lemma34ProofSum_le_corrected (hp : p ≠ ⊤) (φ f : Coeff p) (n : ℤ)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    (∑' lm : ℤ × ℤ, lemma34ProofTerm φ f n r lm) ≤
      (4 * p.toReal ^ 2 / r ^ 2) * (‖φ‖ * ‖f‖) := by
  let a := lemma34Reciprocal hp n hr hr1
  have h := lemma34_weighted_sum_le a a φ f
  have he (lm : ℤ × ℤ) : ‖a lm.1‖ * (‖φ (lm.1+lm.2)‖ * (‖a lm.2‖ * ‖f lm.2‖)) =
      lemma34ProofTerm φ f n r lm := by
    simp only [a, lemma34Reciprocal_norm_apply, lemma34ProofTerm, div_eq_mul_inv, mul_inv]
    ring
  simp only [he] at h
  calc
    _ ≤ (‖a‖ * ‖a‖) * (‖φ‖ * ‖f‖) := h
    _ ≤ ((2 * p.toReal / r) * (2 * p.toReal / r)) * (‖φ‖ * ‖f‖) := by
      gcongr <;> exact norm_lemma34Reciprocal_le hp n hr hr1
    _ = _ := by ring

/-- The near subsum keeps the exact potential tail and the corrected radius exponent two. -/
theorem lemma34ProofNearSum_le_corrected (hp : p ≠ ⊤) (φ f : Coeff p) (n : ℤ)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    lemma34ProofNearSum φ f n r ≤
      (4 * p.toReal ^ 2 / r ^ 2) * (‖Coeff.fourierTail n.natAbs φ‖ * ‖f‖) := by
  rw [← lemma34ProofNearSum_fourierTail φ f n r]
  let ψ := Coeff.fourierTail n.natAbs φ
  have hs := summable_lemma34ProofTerm hp ψ f n hr hr1
  have hn (lm : ℤ × ℤ) : 0 ≤ lemma34ProofTerm ψ f n r lm := by
    unfold lemma34ProofTerm; positivity
  have hle (lm : ℤ × ℤ) : (if lemma34ProofNear n lm.1 lm.2 then
      lemma34ProofTerm ψ f n r lm else 0) ≤ lemma34ProofTerm ψ f n r lm := by
    split_ifs <;> first | exact le_rfl | exact hn lm
  have hm := hs.of_nonneg_of_le (fun lm => by split_ifs <;> first | exact hn lm | exact le_rfl) hle
  exact (hm.tsum_le_tsum hle hs).trans (lemma34ProofSum_le_corrected hp ψ f n hr hr1)

/-- The additive-index weighted absolute sum converges at every Banach endpoint. -/
theorem summable_lemma34WeightedTerms (a b : Coeff p.conjExponent) (φ f : Coeff p) :
    Summable (fun lm : ℤ × ℤ => ‖a lm.1‖ * (‖φ (lm.1+lm.2)‖ * (‖b lm.2‖ * ‖f lm.2‖))) := by
  let e := Equiv.prodCongr (Equiv.refl ℤ) (Equiv.neg ℤ)
  have h := e.summable_iff.mpr (Coeff.summable_sandwich_terms a φ
    (Coeff.reindex (Equiv.neg ℤ) b) (Coeff.reindex (Equiv.neg ℤ) f))
  simpa only [e, Function.comp_def, Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply, Equiv.neg_apply,
    Coeff.reindex_apply, neg_neg, sub_neg_eq_add] using h

/-- The literal far set gains the frequency decay while retaining an inverse-square radius. -/
theorem lemma34ProofFarSum_le_corrected_of_ne_zero (hp : p ≠ ⊤) (φ f : Coeff p)
    (n : ℤ) (hn : n ≠ 0) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    lemma34ProofFarSum φ f n r ≤
      (32 * p.toReal ^ 2 / r ^ 2) * (n.natAbs : ℝ) ^ (-(1 / p.toReal)) * (‖φ‖ * ‖f‖) := by
  let a := lemma34Reciprocal hp n hr hr1
  let A := Coeff.frequencyWindow n (n.natAbs / 2)
  let t := a - Coeff.truncate A a
  have ht (k : ℤ) : t k = if k ∈ A then 0 else a k := by
    change a k - Coeff.truncate A a k = _
    by_cases hk : k ∈ A <;> simp [hk]
  have ha := norm_lemma34Reciprocal_le hp n hr hr1
  have htail : ‖t‖ ≤ (8 * p.toReal / r) * (n.natAbs : ℝ) ^ (-(1 / p.toReal)) := by
    apply Coeff.norm_centered_reciprocal_windowTail_le_simple hp n.natAbs (by omega) n hr
    intro k
    rw [lemma34Reciprocal_norm_apply]
    have he : |((n-k : ℤ) : ℝ)| = |((k-n : ℤ) : ℝ)| := by
      push_cast; exact abs_sub_comm _ _
    rw [he]
    rw [← div_eq_mul_inv, inv_eq_one_div]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hr1 (abs_nonneg (((k-n : ℤ) : ℝ)))]
  have hwindow (k : ℤ) (hk : k ∈ A) : |((k-n : ℤ) : ℝ)| ≤ |(n : ℝ)| / 2 := by
    have hk' := (Coeff.mem_frequencyWindow n (n.natAbs / 2) k).mp hk
    have h : 2 * (k-n).natAbs ≤ n.natAbs := by omega
    have h' : (2 : ℝ) * ((k-n).natAbs : ℝ) ≤ (n.natAbs : ℝ) := by exact_mod_cast h
    simp only [Nat.cast_natAbs, Int.cast_abs] at h'
    linarith
  let T (b c : Coeff p.conjExponent) (lm : ℤ × ℤ) :=
    ‖b lm.1‖ * (‖φ (lm.1+lm.2)‖ * (‖c lm.2‖ * ‖f lm.2‖))
  have hs₁ := summable_lemma34WeightedTerms t a φ f
  have hs₂ := summable_lemma34WeightedTerms a t φ f
  have hterm (lm : ℤ × ℤ) :
      (if ¬ lemma34ProofNear n lm.1 lm.2 then lemma34ProofTerm φ f n r lm else 0) ≤
        T t a lm + T a t lm := by
    by_cases hfar : lemma34ProofNear n lm.1 lm.2
    · simp only [hfar, not_true_eq_false, if_false]
      dsimp [T]; positivity
    · rw [if_pos hfar]
      have hbase : lemma34ProofTerm φ f n r lm = T a a lm := by
        simp only [T, a, lemma34Reciprocal_norm_apply, lemma34ProofTerm, div_eq_mul_inv, mul_inv]
        ring
      rw [hbase]
      by_cases hl : lm.1 ∈ A
      · have hm : lm.2 ∉ A := fun hm => hfar ⟨hwindow _ hm, hwindow _ hl⟩
        simp only [T, ht, if_neg hm, if_pos hl, norm_zero, zero_mul, zero_add]
        exact le_rfl
      · simp only [T, ht, if_neg hl]
        exact le_add_of_nonneg_right (by positivity)
  have hs := (hs₁.add hs₂).of_nonneg_of_le
    (fun lm => by split_ifs <;> first | unfold lemma34ProofTerm; positivity | exact le_rfl) hterm
  have hsum := hs.tsum_le_tsum hterm (hs₁.add hs₂)
  rw [hs₁.tsum_add hs₂] at hsum
  have h := hsum.trans (add_le_add (lemma34_weighted_sum_le t a φ f)
    (lemma34_weighted_sum_le a t φ f))
  calc
    _ ≤ (‖t‖ * ‖a‖) * (‖φ‖ * ‖f‖) + (‖a‖ * ‖t‖) * (‖φ‖ * ‖f‖) := h
    _ ≤ ((8 * p.toReal / r) * (n.natAbs : ℝ) ^ (-(1 / p.toReal)) * (2 * p.toReal / r)) *
        (‖φ‖ * ‖f‖) + ((2 * p.toReal / r) *
        ((8 * p.toReal / r) * (n.natAbs : ℝ) ^ (-(1 / p.toReal)))) * (‖φ‖ * ‖f‖) := by
      gcongr
    _ = _ := by ring

/-- A single exponent-dependent constant bounds the literal far sum for all signed centers. -/
theorem lemma34ProofFarSum_le_corrected (hp : p ≠ ⊤) (φ f : Coeff p) (n : ℤ)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    lemma34ProofFarSum φ f n r ≤
      (64 * p.toReal ^ 2 / r ^ 2) * (r + |(n : ℝ)|) ^ (-(1 / p.toReal)) * (‖φ‖ * ‖f‖) := by
  have hpge : 1 ≤ p.toReal := by
    simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono hp (show 1 ≤ p from Fact.out)
  by_cases hn : n = 0
  · subst n
    have hs := summable_lemma34ProofTerm hp φ f 0 hr hr1
    have hpos (lm : ℤ × ℤ) : 0 ≤ lemma34ProofTerm φ f 0 r lm := by
      unfold lemma34ProofTerm; positivity
    have hle (lm : ℤ × ℤ) : (if ¬ lemma34ProofNear 0 lm.1 lm.2 then
        lemma34ProofTerm φ f 0 r lm else 0) ≤ lemma34ProofTerm φ f 0 r lm := by
      split_ifs <;> first | exact le_rfl | exact hpos lm
    have hm := hs.of_nonneg_of_le (fun lm => by split_ifs <;> first | exact hpos lm | exact le_rfl) hle
    have h := (hm.tsum_le_tsum hle hs).trans (lemma34ProofSum_le_corrected hp φ f 0 hr hr1)
    have hpow : 1 ≤ r ^ (-(1 / p.toReal)) := by
      simpa using Real.rpow_le_rpow_of_nonpos hr hr1 (neg_nonpos.mpr (by positivity) : -(1 / p.toReal) ≤ 0)
    simp only [Int.cast_zero, abs_zero, add_zero]
    apply h.trans
    gcongr
    calc
      4 * p.toReal ^ 2 / r ^ 2 ≤ 64 * p.toReal ^ 2 / r ^ 2 := by gcongr; norm_num
      _ ≤ (64 * p.toReal ^ 2 / r ^ 2) * r ^ (-(1 / p.toReal)) :=
        le_mul_of_one_le_right (by positivity) hpow
  · have hnpos : 0 < (n.natAbs : ℝ) := by exact_mod_cast Int.natAbs_pos.mpr hn
    have habs : (n.natAbs : ℝ) = |(n : ℝ)| := by simp only [Nat.cast_natAbs, Int.cast_abs]
    have hnge : 1 ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
    have hpow : (n.natAbs : ℝ) ^ (-(1 / p.toReal)) ≤
        2 * (r + |(n : ℝ)|) ^ (-(1 / p.toReal)) := by
      apply (Real.rpow_le_rpow_of_nonpos (by positivity : 0 < (r + |(n : ℝ)|) / 2)
        (show (r + |(n : ℝ)|) / 2 ≤ (n.natAbs : ℝ) by rw [habs]; linarith)
        (neg_nonpos.mpr (by positivity) : -(1 / p.toReal) ≤ 0)).trans
      exact Coeff.half_radius_rpow_le hpge (by positivity)
    apply (lemma34ProofFarSum_le_corrected_of_ne_zero hp φ f n hn hr hr1).trans
    calc
      _ ≤ (32 * p.toReal ^ 2 / r ^ 2) *
          (2 * (r + |(n : ℝ)|) ^ (-(1 / p.toReal))) * (‖φ‖ * ‖f‖) := by gcongr
      _ = _ := by ring

end NLS.ZakharovShabat
