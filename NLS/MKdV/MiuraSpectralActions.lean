import NLS.MKdV.MiuraActionContourFamily
import NLS.MKdV.MiuraActionZeroIdentification
import NLS.ZakharovShabat.SourceIndexedActionCosineIntegral

/-! # Actual mKdV spectral actions and their exact zero sets

The action is the source's inverse-energy-weighted integral of the
independently constructed physical Hill primitive on a proved isolating
energy contour. Its positive real gap formula follows by change of
variables and Cauchy boundary calculus; it does not define the action.
-/
noncomputable section
open Set Metric Complex MeasureTheory NLS.ComplexAnalysis NLS.KdV NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

/-- The literal positive real gap representation of J_n. -/
def miuraMKdVGapIntegral (a : ScalarDomain 2) (n : ℕ) : ℝ :=
  ((canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential (sobolevSourceInclusion (a,a)))
      (periodOnePotential_mem _) n).re/Real.pi *
    ∫ θ in (0 : ℝ)..Real.pi,
      (realGapAffinePoint (by simp) (by norm_num) (sobolevSourceInclusion (a,a)) n (Real.cos θ))⁻¹ *
        (Real.sin θ*sourceRealGapCosineProfile (by simp) (by norm_num) (sobolevSourceInclusion (a,a)) n θ))/2

namespace MiuraActionContourFamily
variable {a : ScalarDomain 2} {ha : ∀ n, a.val n = conj (a.val (-n))} (F : MiuraActionContourFamily a ha)

theorem two_mul_action_eq_realIntegral (n : ℕ) (hn : 1 ≤ n) (k : ℤ) :
    2*miuraHillActionContour a k (F.energyContour n) =
      (((canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential (realDiagonalH1Source a ha).val)
        (periodOnePotential_mem _) n).re/Real.pi * ∫ θ in (0 : ℝ)..Real.pi,
          (realGapAffinePoint (by simp) (by norm_num) (realDiagonalH1Source a ha).val n (Real.cos θ))^(2*k-3) *
            (Real.sin θ*sourceRealGapCosineProfile (by simp) (by norm_num)
              (realDiagonalH1Source a ha).val n θ) : ℝ) : ℂ) := by
  have hzero : (0 : ℂ) ∉ closedBall (F.cauchy.discs.center n) (F.radius n) := by
    intro h0
    exact F.zero_not_mem_outer n hn (closedBall_subset_closedBall (F.radius_bounds n).2.le h0)
  obtain ⟨E⟩ := F.cauchy.charts _ F.source_mem
  calc
    _ = sourceLaurentActionContour (by simp) (by norm_num) (realDiagonalH1Source a ha)
        (2*k-2) (F.frequencyContour n) :=
      two_mul_miuraHillActionContour a ha k _ (F.frequencyContour_inside n hn)
    _ = sourceLaurentPrimitiveCircle (by simp) (by norm_num) F.domain n (2*k-2)
        (realDiagonalH1Source a ha).val (F.cauchy.discs.center n) (F.radius n) :=
      sourceLaurentActionContour_circle_eq_local _ _ F.domain n (2*k-2) _ E _ _
        (F.radius_pos n).le (F.circle_rootDomain n) hzero
    _ = _ := by
      simpa only [show 2*k-2-1 = 2*k-3 by ring] using
        F.cauchy.laurentPrimitiveCircle_eq_realIntegral n (2*k-2) _ F.source_mem _
          (F.radius_bounds n).1 (F.radius_bounds n).2 hzero

theorem action_one_eq_gapIntegral (n : ℕ) (hn : 1 ≤ n) :
    miuraHillActionContour a 1 (F.energyContour n) = (miuraMKdVGapIntegral a n : ℂ) := by
  have h := F.two_mul_action_eq_realIntegral n hn 1
  simp only [mul_one,show (2 : ℤ)-3 = -1 by norm_num,zpow_neg_one] at h
  simp only [realDiagonalH1Source] at h
  apply mul_left_cancel₀ (show (2 : ℂ) ≠ 0 by norm_num)
  rw [h]
  unfold miuraMKdVGapIntegral
  push_cast
  ring

end MiuraActionContourFamily

/-- The mKdV action is defined by the actual physical contour (13), not
by a zero criterion or by a restricted NLS action. -/
def miuraMKdVAction (a : ScalarDomain 2) (ha : ∀ n, a.val n = conj (a.val (-n))) (n : ℕ) : ℂ :=
  miuraHillActionContour a 1 ((miuraActionContourFamily a ha).energyContour n)

theorem miuraMKdVAction_eq_gapIntegral (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (n : ℕ) (hn : 1 ≤ n) :
    miuraMKdVAction a ha n = (miuraMKdVGapIntegral a n : ℂ) :=
  (miuraActionContourFamily a ha).action_one_eq_gapIntegral n hn

/-- Every independently chosen checked contour family gives the same
physical action, including collapsed gaps. -/
theorem miuraMKdVAction_independent_family (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (F : MiuraActionContourFamily a ha) (n : ℕ) (hn : 1 ≤ n) :
    miuraHillActionContour a 1 (F.energyContour n) = miuraMKdVAction a ha n :=
  (F.action_one_eq_gapIntegral n hn).trans (miuraMKdVAction_eq_gapIntegral a ha n hn).symm

/-- The inverse-frequency mean value lies in the actual positive gap.
This retains the factor two and never divides by a gap length or action. -/
theorem miuraMKdVGapIntegral_eq_action_div_two_point (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (n : ℕ) (hn : 1 ≤ n) :
    ∃ ζ ∈ Icc (miuraNLSLeft a n).re (miuraNLSRight a n).re,
      miuraMKdVGapIntegral a n = (miuraNLSAction a n).re/(2*ζ) := by
  let φ := realDiagonalH1Source a ha
  let x : ℝ → ℝ := fun θ => realGapAffinePoint (by simp) (by norm_num) φ.val n (Real.cos θ)
  let g : ℝ → ℝ := fun θ => Real.sin θ*sourceRealGapCosineProfile (by simp) (by norm_num) φ.val n θ
  have hpos (θ : ℝ) : 0 < x θ :=
    (miuraNLSLeft_pos a ha (show (0 : ℤ) < n by omega)).trans_le
      (realGapAffinePoint_cos_mem_Icc (by simp) (by norm_num) φ n θ).1
  have hx : Continuous x := by unfold x realGapAffinePoint; fun_prop
  have hc : Continuous (fun θ => (x θ)⁻¹) := hx.inv₀ (fun θ => (hpos θ).ne')
  have hg : Continuous g := Real.continuous_sin.mul (sourceRealGapCosineProfile_continuous _ _ φ n)
  have hnonneg : ∀ θ ∈ uIoc (0 : ℝ) Real.pi, 0 ≤ g θ := by
    intro θ hθ
    rw [uIoc_of_le Real.pi_pos.le] at hθ
    exact mul_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1.le hθ.2)
      (sourceRealGapCosineProfile_nonneg _ _ φ n θ)
  obtain ⟨θ,_,he⟩ := exists_eq_const_mul_intervalIntegral_of_nonneg (μ := volume)
    hc.continuousOn (hg.intervalIntegrable 0 Real.pi) hnonneg
  refine ⟨x θ,realGapAffinePoint_cos_mem_Icc _ _ φ n θ,?_⟩
  have hI := sourceIndexedAction_eq_cosineIntegral (by simp) (by norm_num) φ.val φ.property n
  have hIr := congrArg Complex.re hI
  change (miuraNLSAction a n).re =
    (canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential φ.val)
      (periodOnePotential_mem _) n).re/Real.pi * (∫ θ in (0 : ℝ)..Real.pi, g θ) at hIr
  change ((canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential φ.val)
    (periodOnePotential_mem _) n).re/Real.pi * (∫ θ in (0 : ℝ)..Real.pi, (x θ)⁻¹*g θ))/2 = _
  rw [he,hIr]
  have hxne : x θ ≠ 0 := (hpos θ).ne'
  field_simp

theorem miuraMKdVAction_nonnegative_and_zero_iff (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (n : ℕ) (hn : 1 ≤ n) :
    0 ≤ (miuraMKdVAction a ha n).re ∧ (miuraMKdVAction a ha n).im = 0 ∧
      (miuraMKdVAction a ha n = 0 ↔ miuraNLSAction a n = 0) := by
  obtain ⟨ζ,hζ,hpoint⟩ := miuraMKdVGapIntegral_eq_action_div_two_point a ha n hn
  have hζ : 0 < ζ := (miuraNLSLeft_pos a ha (show (0 : ℤ) < n by omega)).trans_le hζ.1
  have hden : 2*ζ ≠ 0 := (mul_pos (by norm_num : (0 : ℝ) < 2) hζ).ne'
  have hI := miuraNLSAction_nonnegative a ha n
  have hJ := miuraMKdVAction_eq_gapIntegral a ha n hn
  constructor
  · rw [hJ,ofReal_re,hpoint]
    exact div_nonneg hI.1 (mul_pos (by norm_num) hζ).le
  constructor
  · rw [hJ,ofReal_im]
  · constructor
    · intro hz
      have hr := congrArg Complex.re hz
      rw [hJ,ofReal_re,hpoint,zero_re] at hr
      have h0 : (miuraNLSAction a n).re = 0 := (div_eq_zero_iff.mp hr).resolve_right hden
      exact Complex.ext h0 hI.2
    · intro hz
      rw [hJ,hpoint,hz,zero_re,zero_div,ofReal_zero]

end NLS.MKdV
