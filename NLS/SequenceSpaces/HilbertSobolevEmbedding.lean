import NLS.SequenceSpaces.HolderEmbedding
import NLS.SequenceSpaces.SobolevHomogeneous

/-!
# Hilbert Sobolev coefficients at the sharp Hölder threshold

For finite real `q≥1`, the condition `1/q<s+1/2` gives a continuous identity
map from weighted Hilbert coefficients to `ℓ^q`. Exponents at least two use
monotonicity; below two the Hölder exponent is `(1/q-1/2)⁻¹`.
-/

noncomputable section
open scoped ENNReal
namespace NLS

/-- The real auxiliary Hölder exponent for a target below two. -/
def hilbertHolderExponent (q : ℝ) : ℝ := (1 / q - 1 / 2)⁻¹

theorem hilbertHolderExponent_pos {q : ℝ} (hq : 0 < q) (hq₂ : q < 2) :
    0 < hilbertHolderExponent q := by
  apply inv_pos.mpr
  apply sub_pos.mpr
  exact (div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 2) hq).mpr (by linarith)

theorem one_le_hilbertHolderExponent {q : ℝ} (hq : 1 ≤ q) (hq₂ : q < 2) :
    1 ≤ hilbertHolderExponent q := by
  have hd : 0 < 1 / q - 1 / 2 := inv_pos.mp (hilbertHolderExponent_pos (by linarith) hq₂)
  rw [hilbertHolderExponent, one_le_inv₀ hd]
  have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hq
  norm_num only [div_one] at h
  linarith

theorem hilbertHolderExponent_threshold {s q : ℝ} (hq : 0 < q) (hq₂ : q < 2)
    (h : 1 / q < s + 1 / 2) : 1 < s * hilbertHolderExponent q := by
  have hd : 0 < 1 / q - 1 / 2 := inv_pos.mp (hilbertHolderExponent_pos hq hq₂)
  rw [hilbertHolderExponent, ← div_eq_mul_inv, one_lt_div hd]
  linarith

/-- The auxiliary exponent satisfies the exact Hölder relation in extended nonnegative reals. -/
theorem holderTriple_hilbertHolderExponent {q : ℝ} (hq : 0 < q) (hq₂ : q < 2) :
    (2 : ℝ≥0∞).HolderTriple (ENNReal.ofReal (hilbertHolderExponent q)) (ENNReal.ofReal q) := by
  rw [ENNReal.holderTriple_iff]
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num]
  rw [← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2),
    ← ENNReal.ofReal_inv_of_pos (hilbertHolderExponent_pos hq hq₂),
    ← ENNReal.ofReal_inv_of_pos hq,
    ← ENNReal.ofReal_add (by positivity : (0 : ℝ) ≤ (2 : ℝ)⁻¹)
      (inv_nonneg.mpr (hilbertHolderExponent_pos hq hq₂).le)]
  congr 1
  simp only [hilbertHolderExponent, inv_inv, one_div]
  ring

namespace WeightedCoeff

/-- Continuous Sobolev Hilbert embedding into any finite Banach target above the strict threshold. -/
def hilbertSobolevInclusion (s q : ℝ) [Fact (1 ≤ ENNReal.ofReal q)] (hs : 0 ≤ s) (hq : 1 ≤ q) (h : 1 / q < s + 1 / 2) :
    WeightedCoeff (Weight.sobolev s) 2 →L[ℂ] Coeff (ENNReal.ofReal q) := by
  by_cases hq₂ : 2 ≤ q
  · exact (Coeff.exponentInclusion (show (2 : ℝ≥0∞) ≤ ENNReal.ofReal q by
      exact_mod_cast ENNReal.ofReal_le_ofReal hq₂)).comp (sobolevToL2 hs)
  · let r := ENNReal.ofReal (hilbertHolderExponent q)
    have hqpos : 0 < q := by linarith
    have hq₂' : q < 2 := lt_of_not_ge hq₂
    letI : Fact (1 ≤ r) := ⟨by
      exact_mod_cast ENNReal.ofReal_le_ofReal (one_le_hilbertHolderExponent hq hq₂')⟩
    letI : (2 : ℝ≥0∞).HolderTriple r (ENNReal.ofReal q) := holderTriple_hilbertHolderExponent hqpos hq₂'
    have hr : r ≠ ⊤ := ENNReal.ofReal_ne_top
    have ht : 1 < (s - 0) * r.toReal := by
      simpa only [r, sub_zero, ENNReal.toReal_ofReal (hilbertHolderExponent_pos hqpos hq₂').le] using
        hilbertHolderExponent_threshold hqpos hq₂' h
    exact (weightIsometry (Weight.sobolev 0) (ENNReal.ofReal q)).toContinuousLinearEquiv.toContinuousLinearMap.comp
      (sobolevHolderInclusion (r := r) (q := ENNReal.ofReal q) s 0 hr ht)

@[simp] theorem hilbertSobolevInclusion_apply (s q : ℝ) [Fact (1 ≤ ENNReal.ofReal q)] (hs : 0 ≤ s) (hq : 1 ≤ q)
    (h : 1 / q < s + 1 / 2) (a : WeightedCoeff (Weight.sobolev s) 2) (n : ℤ) :
    hilbertSobolevInclusion s q hs hq h a n = a.val n := by
  unfold hilbertSobolevInclusion
  split_ifs with hq₂
  · simp only [ContinuousLinearMap.comp_apply, Coeff.exponentInclusion_apply, sobolevToL2_apply]
  · let : Fact (1 ≤ ENNReal.ofReal (hilbertHolderExponent q)) := ⟨by
      exact_mod_cast ENNReal.ofReal_le_ofReal (one_le_hilbertHolderExponent hq (lt_of_not_ge hq₂))⟩
    let : (2 : ℝ≥0∞).HolderTriple (ENNReal.ofReal (hilbertHolderExponent q)) (ENNReal.ofReal q) :=
      holderTriple_hilbertHolderExponent (by linarith) (lt_of_not_ge hq₂)
    change (Weight.sobolev 0 n : ℂ) * (sobolevHolderInclusion s 0 _ _ a).val n = _
    simp only [sobolevHolderInclusion_apply, Weight.sobolev_apply, Real.rpow_zero, Complex.ofReal_one, one_mul]

/-- The embedding preserves distinct raw coefficient sequences. -/
theorem hilbertSobolevInclusion_injective (s q : ℝ) [Fact (1 ≤ ENNReal.ofReal q)]
    (hs : 0 ≤ s) (hq : 1 ≤ q) (h : 1 / q < s + 1 / 2) :
    Function.Injective (hilbertSobolevInclusion s q hs hq h) := by
  intro a b hab
  apply Subtype.ext
  funext n
  simpa only [hilbertSobolevInclusion_apply] using
    congrArg (fun c : Coeff (ENNReal.ofReal q) => c n) hab

/-- Membership in the sharp Hölder range, preserving raw Fourier coefficients. -/
theorem memlp_of_hilbertSobolev {s q : ℝ} (hs : 0 ≤ s) (hq : 1 ≤ q) (h : 1 / q < s + 1 / 2)
    (a : WeightedCoeff (Weight.sobolev s) 2) : Memℓp a.val (ENNReal.ofReal q) := by
  let : Fact (1 ≤ ENNReal.ofReal q) := ⟨by exact_mod_cast ENNReal.ofReal_le_ofReal hq⟩
  have he : ⇑(hilbertSobolevInclusion s q hs hq h a) = a.val := by
    funext n
    exact hilbertSobolevInclusion_apply s q hs hq h a n
  rw [← he]
  exact lp.memℓp _

end WeightedCoeff
end NLS
