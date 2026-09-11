import NLS.SequenceSpaces.FourierTail
import NLS.SequenceSpaces.ReciprocalNorm
import NLS.SequenceSpaces.Translation

/-!
# Reciprocal-symbol decay outside a frequency window

Appendix B.1 bounds the conjugate-space norm of a reciprocal symbol after
removing a window of half the cutoff radius. This includes the supremum-norm
endpoint and supplies the `N^(-1/p)` factor in Lemma 3.4.
-/

open scoped ENNReal
noncomputable section

namespace NLS.Coeff

private theorem half_cutoff_lt_abs {N : ℕ} {k : ℤ} (hk : ¬ k.natAbs ≤ N / 2) :
    (N : ℝ) / 2 < |(k : ℝ)| := by
  have h : N < 2 * k.natAbs := by omega
  have h' : (N : ℝ) < 2 * (k.natAbs : ℝ) := by exact_mod_cast h
  have he : (k.natAbs : ℝ) = |(k : ℝ)| := by simp only [Nat.cast_natAbs, Int.cast_abs]
  rw [he] at h'
  linarith

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Removing the half-radius window from a normalized reciprocal symbol gives
an explicit decaying conjugate-space norm. -/
theorem norm_reciprocal_windowTail_le (hp : p ≠ ⊤) (N : ℕ) (hN : 0 < N)
    (a : Coeff p.conjExponent) (ha : ∀ k : ℤ, ‖a k‖ ≤ (1 + |(k : ℝ)|)⁻¹) :
    ‖a - truncate (frequencyWindow 0 (N / 2)) a‖ ≤
      4 * p.toReal * ((N : ℝ) / 2) ^ (-(1 / p.toReal)) := by
  let : Fact (1 ≤ p.conjExponent) := ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩
  let b := a - truncate (frequencyWindow 0 (N / 2)) a
  have hb (k : ℤ) : b k = if k.natAbs ≤ N / 2 then 0 else a k := by
    change a k - truncate (frequencyWindow 0 (N / 2)) a k = _
    by_cases hk : k.natAbs ≤ N / 2 <;> simp [hk]
  have hNr : 0 < (N : ℝ) / 2 := by positivity
  have hb0 : b 0 = 0 := by simp [hb]
  have hbmajor (k : ℤ) : ‖b k‖ ≤ 2 / ((N : ℝ) / 2 + |(k : ℝ)|) := by
    rw [hb]
    split_ifs with hk
    · simp only [norm_zero]
      positivity
    · have hk' := half_cutoff_lt_abs hk
      refine (ha k).trans ?_
      rw [inv_eq_one_div]
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      linarith [abs_nonneg (k : ℝ)]
  by_cases hp1 : p = 1
  · subst p
    change ‖b‖ ≤ _
    have hinfty {q : ℝ≥0∞} (hq : q = ⊤) (c : Coeff q)
        (hc : ∀ k : ℤ, ‖c k‖ ≤ 2 / ((N : ℝ) / 2 + |(k : ℝ)|)) :
        ‖c‖ ≤ 2 / ((N : ℝ) / 2) := by
      subst q
      apply lp.norm_le_of_forall_le (by positivity)
      intro k
      exact (hc k).trans (div_le_div_of_nonneg_left (by norm_num) hNr (by linarith [abs_nonneg (k : ℝ)]))
    have hbound := hinfty (q := (1 : ℝ≥0∞).conjExponent) (by simp [ENNReal.conjExponent]) b hbmajor
    norm_num only [ENNReal.toReal_one, div_one, Real.rpow_neg_one, mul_one]
    simpa only [div_eq_mul_inv] using hbound.trans
      (show 2 / ((N : ℝ) / 2) ≤ 4 / ((N : ℝ) / 2) by gcongr; norm_num)
  · have hpg : 1 < p := lt_of_le_of_ne Fact.out (Ne.symm hp1)
    have hq : p.conjExponent ≠ ⊤ := ne_of_lt
      ((ENNReal.HolderConjugate.lt_top_iff_one_lt p.conjExponent p).mpr hpg)
    exact norm_punctured_reciprocal_le
      (ENNReal.HolderConjugate.toReal_of_ne_top hp hq) hNr b hb0 (fun k _ => hbmajor k)

/-- The same estimate after recentering and rescaling the reciprocal envelope. -/
theorem norm_centered_reciprocal_windowTail_le (hp : p ≠ ⊤) (N : ℕ) (hN : 0 < N)
    (c : ℤ) {r : ℝ} (hr : 0 < r) (a : Coeff p.conjExponent)
    (ha : ∀ k : ℤ, r * ‖a k‖ ≤ (1 + |((k - c : ℤ) : ℝ)|)⁻¹) :
    ‖a - truncate (frequencyWindow c (N / 2)) a‖ ≤
      (4 * p.toReal / r) * ((N : ℝ) / 2) ^ (-(1 / p.toReal)) := by
  let : Fact (1 ≤ p.conjExponent) := ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩
  let b : Coeff p.conjExponent := (r : ℂ) • reindex (Equiv.addRight c) a
  have hb (k : ℤ) : ‖b k‖ ≤ (1 + |(k : ℝ)|)⁻¹ := by
    change ‖(r : ℂ) * a (k + c)‖ ≤ _
    simpa [Complex.norm_real, abs_of_pos hr, norm_mul] using ha (k + c)
  have he : b - truncate (frequencyWindow 0 (N / 2)) b =
      (r : ℂ) • reindex (Equiv.addRight c) (a - truncate (frequencyWindow c (N / 2)) a) := by
    ext k
    change b k - truncate (frequencyWindow 0 (N / 2)) b k =
      (r : ℂ) * (a (k + c) - truncate (frequencyWindow c (N / 2)) a (k + c))
    have hbk : b k = (r : ℂ) * a (k + c) := rfl
    by_cases hk : k.natAbs ≤ N / 2 <;> simp [hk, hbk]
  have hn := norm_reciprocal_windowTail_le hp N hN b hb
  rw [he, norm_smul, norm_reindex, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] at hn
  calc
    _ ≤ (4 * p.toReal * ((N : ℝ) / 2) ^ (-(1 / p.toReal))) / r :=
      (le_div_iff₀ hr).mpr (by simpa only [mul_comm] using hn)
    _ = _ := by ring

/-- Replacing a half-radius power by a full-radius power costs at most two
at Banach exponents. -/
theorem half_radius_rpow_le {s x : ℝ} (hs : 1 ≤ s) (hx : 0 ≤ x) :
    (x / 2) ^ (-(1 / s)) ≤ 2 * x ^ (-(1 / s)) := by
  have hs0 : 0 < s := zero_lt_one.trans_le hs
  have ht : 1 / s ≤ 1 := (div_le_one hs0).mpr hs
  have htwo : (2 : ℝ) ^ (1 / s) ≤ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) ht
  calc
    _ = x ^ (-(1 / s)) * (2 : ℝ) ^ (1 / s) := by
      rw [Real.div_rpow hx (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
        div_inv_eq_mul]
    _ ≤ x ^ (-(1 / s)) * 2 :=
      mul_le_mul_of_nonneg_left htwo (Real.rpow_nonneg hx _)
    _ = _ := by ring

/-- A full-radius `N^(-1/p)` form of the centered reciprocal-tail bound. -/
theorem norm_centered_reciprocal_windowTail_le_simple (hp : p ≠ ⊤) (N : ℕ) (hN : 0 < N)
    (c : ℤ) {r : ℝ} (hr : 0 < r) (a : Coeff p.conjExponent)
    (ha : ∀ k : ℤ, r * ‖a k‖ ≤ (1 + |((k - c : ℤ) : ℝ)|)⁻¹) :
    ‖a - truncate (frequencyWindow c (N / 2)) a‖ ≤
      (8 * p.toReal / r) * (N : ℝ) ^ (-(1 / p.toReal)) := by
  have hp1 : 1 ≤ p.toReal := by
    simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono hp (show 1 ≤ p from Fact.out)
  calc
    _ ≤ (4 * p.toReal / r) * ((N : ℝ) / 2) ^ (-(1 / p.toReal)) :=
      norm_centered_reciprocal_windowTail_le hp N hN c hr a ha
    _ ≤ (4 * p.toReal / r) * (2 * (N : ℝ) ^ (-(1 / p.toReal))) :=
      mul_le_mul_of_nonneg_left (half_radius_rpow_le hp1 (by positivity)) (by positivity)
    _ = _ := by ring

end NLS.Coeff
