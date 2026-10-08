import NLS.SequenceSpaces.SpectralWeight
import Mathlib.Analysis.Real.Pi.Bounds

/-! # The weight class M₁ in Section 25

A member is a spectral weight with an exact factor ⟨n⟩=1+|n|, leaving
another normalized monotone submultiplicative spectral weight.
-/
noncomputable section
namespace NLS.SpectralWeight

/-- Pointwise products preserve all four spectral weight conditions. -/
def mul (v w : SpectralWeight) : SpectralWeight where
  value k := v k*w k
  positive k := mul_pos (v.positive k) (w.positive k)
  one_le k := by nlinarith [v.one_le k, w.one_le k]
  neg_eq k := by rw [v.apply_neg, w.apply_neg]
  add_le k l := by
    calc
      _ ≤ (v k*v l)*(w k*w l) := mul_le_mul (v.add_le k l) (w.add_le k l)
        (w.positive _).le (mul_nonneg (v.positive _).le (v.positive _).le)
      _ = _ := by ring
  monotone_nat k l h := mul_le_mul (v.monotone_nat h) (w.monotone_nat h)
    (w.positive _).le (v.positive _).le

@[simp] theorem mul_apply (v w : SpectralWeight) (k : ℤ) : v.mul w k = v k*w k := rfl

/-- Add the linear bracket required in Chapter 5. -/
def withLinearFactor (v : SpectralWeight) : SpectralWeight := (sobolev 1 (by norm_num)).mul v

@[simp] theorem withLinearFactor_apply (v : SpectralWeight) (k : ℤ) :
    v.withLinearFactor k = (1+|(k:ℝ)|)*v k := by
  simp [withLinearFactor, Weight.sobolev_apply]

/-- The exact factorization condition defining the class M₁. -/
def HasLinearFactor (w : SpectralWeight) : Prop := ∃ v : SpectralWeight, ∀ k, w k = (1+|(k:ℝ)|)*v k

theorem hasLinearFactor_withLinearFactor (v : SpectralWeight) : v.withLinearFactor.HasLinearFactor :=
  ⟨v, withLinearFactor_apply v⟩

theorem bracket_le_of_hasLinearFactor {w : SpectralWeight} (hw : w.HasLinearFactor) (k : ℤ) :
    1+|(k:ℝ)| ≤ w k := by
  obtain ⟨v,hv⟩ := hw
  rw [hv]
  exact le_mul_of_one_le_right (by positivity) (v.one_le k)

/-- The weight gain used before the double Cauchy–Schwarz estimate. -/
theorem linear_shift_ratio {w : SpectralWeight} (hw : w.HasLinearFactor) (j k i : ℤ) :
    w (j+i) ≤ (1+|((j+i:ℤ):ℝ)|)/((1+|((j-k:ℤ):ℝ)|)*(1+|((k+i:ℤ):ℝ)|))*
      w (j-k)*w (k+i) := by
  obtain ⟨v,hv⟩ := hw
  rw [hv, hv, hv]
  have h := mul_le_mul_of_nonneg_left (v.add_le (j-k) (k+i))
    (by positivity : 0 ≤ 1+|((j+i:ℤ):ℝ)|)
  rw [show j-k+(k+i)=j+i by omega] at h
  calc
    _ ≤ (1+|((j+i:ℤ):ℝ)|)*(v (j-k)*v (k+i)) := h
    _ = _ := by
      have hA : (1+|((j-k:ℤ):ℝ)|) ≠ 0 := ne_of_gt (by positivity)
      have hB : (1+|((k+i:ℤ):ℝ)|) ≠ 0 := ne_of_gt (by positivity)
      field_simp

/-- The signed Fourier-coordinate form appearing explicitly in Lemma 25.2. -/
theorem linear_signed_ratio {w : SpectralWeight} (hw : w.HasLinearFactor) (n k l : ℤ) :
    w (k-n) ≤ (1+|((k-n:ℤ):ℝ)|)/((1+|((k+l:ℤ):ℝ)|)*(1+|((l+n:ℤ):ℝ)|))*
      w (k+l)*w (-l-n) := by
  have h := linear_shift_ratio hw k (-l) (-n)
  simpa only [sub_neg_eq_add, ← sub_eq_add_neg, show -l-n=-(l+n) by omega,
    Int.cast_neg, abs_neg] using h

/-- Every normalized Sobolev weight of order at least one belongs to M₁. -/
theorem hasLinearFactor_sobolev (s : ℝ) (hs : 1 ≤ s) :
    (sobolev s (zero_le_one.trans hs)).HasLinearFactor := by
  refine ⟨sobolev (s-1) (sub_nonneg.mpr hs), fun k => ?_⟩
  simp only [sobolev_apply, Weight.sobolev_apply]
  have h := Real.rpow_add (by positivity : 0 < 1+|(k:ℝ)|) 1 (s-1)
  simpa only [show 1+(s-1)=s by ring, Real.rpow_one] using h

private theorem linearRatio_mono {c x y : ℝ} (hc : 1 ≤ c) (hx : 0 ≤ x) (hxy : x ≤ y) :
    (1+c*x)/(1+x) ≤ (1+c*y)/(1+y) := by
  apply (div_le_div_iff₀ (by positivity) (by linarith)).mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr hc) (sub_nonneg.mpr hxy)]

/-- The residual spectral weight after removing ⟨n⟩ from ⟨cn⟩, for c≥1. -/
def linearRatio (c : ℝ) (hc : 1 ≤ c) : SpectralWeight where
  value k := (1+c*|(k:ℝ)|)/(1+|(k:ℝ)|)
  positive k := div_pos (by nlinarith [abs_nonneg (k:ℝ)]) (by positivity)
  one_le k := by
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith [abs_nonneg (k:ℝ)]
  neg_eq k := by simp
  add_le k l := by
    have hx : 0 ≤ |(k:ℝ)| := abs_nonneg _
    have hy : 0 ≤ |(l:ℝ)| := abs_nonneg _
    have ht : |((k+l:ℤ):ℝ)| ≤ |(k:ℝ)|+|(l:ℝ)| := by simpa using abs_add_le (k:ℝ) (l:ℝ)
    calc
      _ ≤ (1+c*(|(k:ℝ)|+|(l:ℝ)|))/(1+(|(k:ℝ)|+|(l:ℝ)|)) :=
        linearRatio_mono hc (abs_nonneg _) ht
      _ ≤ _ := by
        have hA : 0 < 1+|(k:ℝ)| := by positivity
        have hB : 0 < 1+|(l:ℝ)| := by positivity
        rw [div_mul_div_comm]
        apply (div_le_div_iff₀ (by positivity) (mul_pos hA hB)).mpr
        have h := mul_nonneg (mul_nonneg (mul_nonneg (sub_nonneg.mpr hc) hx) hy)
          (show 0 ≤ (c+1)+c*(|(k:ℝ)|+|(l:ℝ)|) by positivity)
        nlinarith
  monotone_nat k l h := by
    simp only [Int.cast_natCast, Nat.abs_cast]
    exact linearRatio_mono hc (Nat.cast_nonneg k) (by exact_mod_cast h)

/-- Scaled Sobolev weights include the dissertation's exact π normalization. -/
theorem hasLinearFactor_scaledSobolev (c s : ℝ) (hc : 1 ≤ c) (hs : 1 ≤ s) :
    (scaledSobolev c s (zero_le_one.trans hc) (zero_le_one.trans hs)).HasLinearFactor := by
  refine ⟨(linearRatio c hc).mul (scaledSobolev c (s-1) (zero_le_one.trans hc) (sub_nonneg.mpr hs)), fun k => ?_⟩
  simp only [scaledSobolev_apply, mul_apply, linearRatio]
  have hp : 0 < 1+c*|(k:ℝ)| := by nlinarith [abs_nonneg (k:ℝ)]
  have h := Real.rpow_add hp 1 (s-1)
  rw [show 1+(s-1)=s by ring, Real.rpow_one] at h
  rw [h]
  field_simp

/-- In particular, the exact source weights ⟨nπ⟩ˢ belong to M₁ for s≥1. -/
theorem hasLinearFactor_piSobolev (s : ℝ) (hs : 1 ≤ s) :
    (piSobolev s (zero_le_one.trans hs)).HasLinearFactor := by
  have hc : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
  exact hasLinearFactor_scaledSobolev Real.pi s hc hs

end NLS.SpectralWeight
