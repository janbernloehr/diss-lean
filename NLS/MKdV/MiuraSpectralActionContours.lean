import NLS.MKdV.MiuraSpectralActions
import NLS.ZakharovShabat.SourceLaurentActionContourPeriod

/-! # Indexed physical mKdV contours, integer levels and winding independence

The actual energy circuits lie in the physical Hill gap complement,
wind once about the intended intrinsic Hill gap, and exclude the origin
and other positive gaps. Every close piecewise circuit has the exact
integer-level period formula; winding one gives the same physical action.
-/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis NLS.KdV NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

def miuraMKdVActionLevel (a : ScalarDomain 2) (ha : ∀ n, a.val n = conj (a.val (-n)))
    (n : ℕ) (k : ℤ) : ℂ := miuraHillActionContour a k ((miuraActionContourFamily a ha).energyContour n)

@[simp] theorem miuraMKdVActionLevel_one (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (n : ℕ) :
    miuraMKdVActionLevel a ha n 1 = miuraMKdVAction a ha n := rfl

namespace MiuraActionContourFamily
variable {a : ScalarDomain 2} {ha : ∀ n, a.val n = conj (a.val (-n))} (F : MiuraActionContourFamily a ha)

theorem energyContour_winding_Hill_gap (n : ℕ) (hn : 1 ≤ n) (μ : ℝ)
    (hμ : μ ∈ Icc (miuraHillLabels a ha (2*n-1)) (miuraHillLabels a ha (2*n))) :
    (F.energyContour n).windingIntegral (μ : ℂ) = 1 := by
  have hi : μ ∈ (fun x : ℝ => x^2) '' Icc (miuraNLSLeft a n).re (miuraNLSRight a n).re := by
    rw [miuraHillGap_square_image a ha n hn]
    exact hμ
  obtain ⟨x,hx,he⟩ := hi
  have hc : (x : ℂ)^2 = (μ : ℂ) := by exact_mod_cast he
  simpa only [hc] using F.energyContour_winding_gap n hn x hx

theorem energyContour_winding_other_Hill_gap (n : ℕ) (hn : 1 ≤ n) (m : ℕ) (hm : 1 ≤ m)
    (hmn : m ≠ n) (μ : ℝ)
    (hμ : μ ∈ Icc (miuraHillLabels a ha (2*m-1)) (miuraHillLabels a ha (2*m))) :
    (F.energyContour n).windingIntegral (μ : ℂ) = 0 := by
  have hi : μ ∈ (fun x : ℝ => x^2) '' Icc (miuraNLSLeft a m).re (miuraNLSRight a m).re := by
    rw [miuraHillGap_square_image a ha m hm]
    exact hμ
  obtain ⟨x,hx,he⟩ := hi
  have hc : (x : ℂ)^2 = (μ : ℂ) := by exact_mod_cast he
  simpa only [hc] using F.energyContour_winding_other_gap n hn m hm hmn x hx

theorem closeContour_inside (n : ℕ) (hn : 1 ≤ n) (Γ : PiecewiseC1Loop)
    (hΓ : Γ.Inside (ball (F.cauchy.discs.center n) (F.cauchy.discs.outer n) \
      sourcePeriodicSegment (by simp) (by norm_num) (realDiagonalH1Source a ha).val n)) :
    Γ.Inside (miuraRightFrequencyDomain a) := by
  intro i u
  have hz := hΓ i u
  refine ⟨F.outer_disc_right n hn _ (ball_subset_closedBall hz.1),?_⟩
  intro m
  by_cases hm : m = (n : ℤ)
  · subst m; exact hz.2
  · exact F.cauchy.discs.avoids_other _ F.source_mem n (ball_subset_closedBall hz.1) m hm

theorem actionLevel_independent_family (n : ℕ) (hn : 1 ≤ n) (k : ℤ) :
    miuraHillActionContour a k (F.energyContour n) = miuraMKdVActionLevel a ha n k := by
  apply mul_left_cancel₀ (show (2 : ℂ) ≠ 0 by norm_num)
  exact (F.two_mul_action_eq_realIntegral n hn k).trans
    ((miuraActionContourFamily a ha).two_mul_action_eq_realIntegral n hn k).symm

/-- Every integer level has its actual period formula on arbitrary
close piecewise C¹ circuits, including corners and repeated traversals. -/
theorem actionContour_eq_mul_winding (n : ℕ) (hn : 1 ≤ n) (k : ℤ) (Γ : PiecewiseC1Loop)
    (hΓ : Γ.Inside (ball (F.cauchy.discs.center n) (F.cauchy.discs.outer n) \
      sourcePeriodicSegment (by simp) (by norm_num) (realDiagonalH1Source a ha).val n)) :
    miuraHillActionContour a k Γ.square = miuraMKdVActionLevel a ha n k *
      Γ.windingIntegral (canonicalPeriodicMidpoint (by simp) (by norm_num)
        (periodOnePotential (realDiagonalH1Source a ha).val) (periodOnePotential_mem _) n) := by
  obtain ⟨E⟩ := F.cauchy.charts _ F.source_mem
  have hzero : (0 : ℂ) ∉ closedBall (F.cauchy.discs.center n) (F.radius n) := by
    intro h0
    exact F.zero_not_mem_outer n hn (closedBall_subset_closedBall (F.radius_bounds n).2.le h0)
  have hlocal := sourceLaurentActionContour_circle_eq_local (by simp) (by norm_num) F.domain n (2*k-2)
    (realDiagonalH1Source a ha) E (F.cauchy.discs.center n) (F.radius n) (F.radius_pos n).le
      (F.circle_rootDomain n) hzero
  have hperiod := F.cauchy.laurentActionContour_eq_mul_winding n (2*k-2) _ F.source_mem _
    (F.radius_bounds n).1 (F.radius_bounds n).2 (F.zero_not_mem_outer n hn) Γ hΓ
  have hΓeq := two_mul_miuraHillActionContour a ha k Γ (F.closeContour_inside n hn Γ hΓ)
  have hcircle := two_mul_miuraHillActionContour a ha k _ (F.frequencyContour_inside n hn)
  have hcLocal : 2*miuraHillActionContour a k (F.energyContour n) =
      sourceLaurentPrimitiveCircle (by simp) (by norm_num) F.domain n (2*k-2)
        (realDiagonalH1Source a ha).val (F.cauchy.discs.center n) (F.radius n) := hcircle.trans hlocal
  apply mul_left_cancel₀ (show (2 : ℂ) ≠ 0 by norm_num)
  rw [hΓeq,hperiod,← hcLocal,← F.actionLevel_independent_family n hn k]
  ring

end MiuraActionContourFamily

/-- The literal integer-level mKdV contour and its required NLS level. -/
theorem miuraMKdVActionLevel_eq_NLSLaurent (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (n : ℕ) (hn : 1 ≤ n) (k : ℤ) :
    2*miuraMKdVActionLevel a ha n k = sourceLaurentActionContour (by simp) (by norm_num)
      (realDiagonalH1Source a ha) (2*k-2) ((miuraActionContourFamily a ha).frequencyContour n) :=
  two_mul_miuraHillActionContour a ha k _ ((miuraActionContourFamily a ha).frequencyContour_inside n hn)

/-- Source (13), with an actual certified energy circuit for each positive gap. -/
theorem miuraMKdVAction_physical_contour (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (n : ℕ) (hn : 1 ≤ n) :
    ∃ energyLoop : PiecewiseC1Loop,
      energyLoop.Inside (miuraHillGapComplement a ha) ∧ energyLoop.windingIntegral 0 = 0 ∧
      (∀ μ ∈ Icc (miuraHillLabels a ha (2*n-1)) (miuraHillLabels a ha (2*n)),
        energyLoop.windingIntegral (μ : ℂ) = 1) ∧
      (∀ m : ℕ, 1 ≤ m → m ≠ n → ∀ μ ∈ Icc (miuraHillLabels a ha (2*m-1)) (miuraHillLabels a ha (2*m)),
        energyLoop.windingIntegral (μ : ℂ) = 0) ∧
      miuraMKdVAction a ha n = -(4*(Real.pi : ℂ))⁻¹ *
        energyLoop.integral (fun μ => μ⁻¹*canonicalMiuraHillPrimitive a μ) := by
  let F := miuraActionContourFamily a ha
  refine ⟨F.energyContour n,F.energyContour_inside n hn,F.energyContour_winding_zero n hn,
    F.energyContour_winding_Hill_gap n hn,?_,?_⟩
  · intro m hm hmn μ hμ
    exact F.energyContour_winding_other_Hill_gap n hn m hm hmn μ hμ
  · simp only [miuraMKdVAction,miuraHillActionContour,show (1 : ℤ)-2 = -1 by norm_num,zpow_neg_one,F]

end NLS.MKdV
