import NLS.ZakharovShabat.ResonantRootGap
import NLS.ZakharovShabat.ResonantLeadingPowerTail
import NLS.ZakharovShabat.OffDiagonalSummability
import NLS.ZakharovShabat.RootDisplacementPower

/-!
# A weighted gap majorant retaining the leading Fourier coefficients

The factor-six squared gap bound and weighted full-strip coefficient bounds
imply a power majorant involving only the leading modes and off-diagonal
remainders. The deliberately loose exponent-only constant avoids the
source's intermediate power-mean constants and works also above exponent two.
-/

noncomputable section
open scoped ENNReal NNReal
namespace NLS.ZakharovShabat

/-- An explicit exponent-only constant for splitting the two full coefficients. -/
def rootGapSummationConstant (p : ℝ≥0∞) : ℝ :=
  (2 : ℝ)^p.toReal * ((2 : ℝ)^(p.toReal-1))^2

theorem rootGapSummationConstant_nonneg (p : ℝ≥0∞) : 0 ≤ rootGapSummationConstant p := by
  unfold rootGapSummationConstant
  positivity

/-- A convenient power-mean bound for nonnegative real inputs. -/
theorem nonneg_add_rpow_le {P a b : ℝ} (hP : 1 ≤ P) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a+b)^P ≤ (2 : ℝ)^(P-1)*(a^P+b^P) := by
  exact_mod_cast NNReal.rpow_add_le_mul_rpow_add_rpow (⟨a,ha⟩ : ℝ≥0) (⟨b,hb⟩ : ℝ≥0) hP

/-- A squared product bound gives a four-term power estimate without square-root branches. -/
theorem gap_rpow_le_four_terms {P d l m r s : ℝ} (hP : 1 ≤ P)
    (hd : 0 ≤ d) (hl : 0 ≤ l) (hm : 0 ≤ m) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hgap : d^2 ≤ 6*(l+r)*(m+s)) :
    d^P ≤ (2 : ℝ)^P * ((2 : ℝ)^(P-1))^2 * (l^P+m^P+r^P+s^P) := by
  have hlin : d ≤ 2*((l+r)+(m+s)) := by
    nlinarith [sq_nonneg ((l+r)-(m+s)), sq_nonneg (d-2*((l+r)+(m+s)))]
  have hfirst := nonneg_add_rpow_le hP (add_nonneg hl hr) (add_nonneg hm hs)
  have hleft := nonneg_add_rpow_le hP hl hr
  have hright := nonneg_add_rpow_le hP hm hs
  calc
    d^P ≤ (2*((l+r)+(m+s)))^P := Real.rpow_le_rpow hd hlin (zero_le_one.trans hP)
    _ = (2 : ℝ)^P * (((l+r)+(m+s))^P) := Real.mul_rpow (by positivity) (by positivity)
    _ ≤ (2 : ℝ)^P * ((2 : ℝ)^(P-1)*((l+r)^P+(m+s)^P)) :=
      mul_le_mul_of_nonneg_left hfirst (by positivity)
    _ ≤ (2 : ℝ)^P * ((2 : ℝ)^(P-1)*
        ((2 : ℝ)^(P-1)*(l^P+r^P)+(2 : ℝ)^(P-1)*(m^P+s^P))) := by
      gcongr
    _ = _ := by ring

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Weighted leading powers and actual weighted remainder suprema. -/
def resonantGapMajorant (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) : ℝ :=
  rootGapSummationConstant p * (resonantLeadingPower w φ n +
    (resonantBMinusRemainderSup hp w φ n)^p.toReal +
    (resonantBPlusRemainderSup hp w φ n)^p.toReal)

/-- Weighted full coefficient bounds control the unweighted product supremum. -/
theorem weighted_resonantBProductSup_le (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (B C : ℝ) (hB : 0 ≤ B)
    (hb : ∀ z ∈ resonantStrip n,
      w (2*n)*‖weightedResonantBMinusExtension hp w φ n z‖ ≤ B ∧
      w (2*n)*‖weightedResonantBPlusExtension hp w φ n z‖ ≤ C) :
    (w (2*n))^2 * resonantBProductSup hp w φ n ≤ B*C := by
  have hw : 0 < w (2*n) := lt_of_lt_of_le zero_lt_one (w.one_le _)
  have hpoint (z : ℂ) (hz : z ∈ resonantStrip n) :
      SpectralWeight.one (2*n) * ‖weightedResonantBPlusExtension hp w φ n z *
        weightedResonantBMinusExtension hp w φ n z‖ ≤ B*C/(w (2*n))^2 := by
    simp only [SpectralWeight.one_apply, one_mul, norm_mul]
    apply (le_div_iff₀ (sq_pos_of_pos hw)).mpr
    have hh := mul_le_mul (hb z hz).1 (hb z hz).2 (by positivity) hB
    nlinarith
  have hsup := (weightedStripSup_bounds SpectralWeight.one n _ _ hpoint).2.1
  change resonantBProductSup hp w φ n ≤ B*C/(w (2*n))^2 at hsup
  have hh := (le_div_iff₀ (sq_pos_of_pos hw)).mp hsup
  nlinarith

/-- Every pair with the actual squared gap bound is controlled by the weighted majorant. -/
theorem resonantRoots_gap_le_majorant (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ)
    (hm : 0 ≤ resonantBMinusRemainderSup hp w φ n)
    (hp' : 0 ≤ resonantBPlusRemainderSup hp w φ n)
    (hb : ∀ z ∈ resonantStrip n,
      w (2*n)*‖weightedResonantBMinusExtension hp w φ n z-φ.fst.val (-(2*n))‖ ≤ resonantBMinusRemainderSup hp w φ n ∧
      w (2*n)*‖weightedResonantBPlusExtension hp w φ n z-φ.snd.val (2*n)‖ ≤ resonantBPlusRemainderSup hp w φ n)
    (x y : ℂ) (hgap : ‖x-y‖^2 ≤ 6*resonantBProductSup hp w φ n) :
    (w (2*n)*‖x-y‖)^p.toReal ≤ resonantGapMajorant hp w φ n := by
  have hw : 0 ≤ w (2*n) := zero_le_one.trans (w.one_le _)
  have hfull := weighted_resonantBProductSup_le hp w φ n
    (w (2*n)*‖φ.fst.val (-(2*n))‖+resonantBMinusRemainderSup hp w φ n)
    (w (2*n)*‖φ.snd.val (2*n)‖+resonantBPlusRemainderSup hp w φ n)
    (by positivity) (fun z hz => by
      have hm' := mul_le_mul_of_nonneg_left (norm_le_norm_sub_add
        (weightedResonantBMinusExtension hp w φ n z) (φ.fst.val (-(2*n)))) hw
      have hp'' := mul_le_mul_of_nonneg_left (norm_le_norm_sub_add
        (weightedResonantBPlusExtension hp w φ n z) (φ.snd.val (2*n))) hw
      have hh := hb z hz
      constructor <;> nlinarith)
  have hP : 1 ≤ p.toReal := (ENNReal.toReal_le_toReal (by simp) hp).mpr (show 1 ≤ p from Fact.out)
  apply gap_rpow_le_four_terms hP (by positivity) (by positivity) (by positivity) hm hp'
  have hg := mul_le_mul_of_nonneg_left hgap (sq_nonneg (w (2*n)))
  nlinarith

end NLS.ZakharovShabat
