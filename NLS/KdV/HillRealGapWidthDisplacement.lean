import NLS.KdV.HminusOneHillPsiZeroSequenceContinuity

/-! The full original energy gap width, divided by its positive index,
is a continuous l2 sequence. It bounds differences of arbitrary points
in the same gap, with every low and collapsed gap retained. -/
noncomputable section
open Set Complex
open scoped ENNReal Classical
namespace NLS.KdV

def hillHminusGapWidthDisplacement (q : PeriodOneRealHminusOne) : lp (fun _ : ℕ+ => ℂ) 2 :=
  hillHminusPositiveEndpointDisplacement true q-hillHminusPositiveEndpointDisplacement false q

theorem hillHminusGapWidthDisplacement_apply (q : PeriodOneRealHminusOne) (m : ℕ+) :
    hillHminusGapWidthDisplacement q m =
      ((hillHminusLabels q.val q.property (2*(m:ℕ)):ℂ)-
        (hillHminusLabels q.val q.property (2*(m:ℕ)-1):ℂ))/(m:ℕ) := by
  change ((hillHminusLabels q.val q.property (2*(m:ℕ)):ℂ)-((Real.pi:ℂ)*(m:ℕ))^2)/(m:ℕ)-
    ((hillHminusLabels q.val q.property (2*(m:ℕ)-1):ℂ)-((Real.pi:ℂ)*(m:ℕ))^2)/(m:ℕ) = _
  ring

theorem continuous_hillHminusGapWidthDisplacement : Continuous hillHminusGapWidthDisplacement :=
  (continuous_hillHminusPositiveEndpointDisplacement true).sub
    (continuous_hillHminusPositiveEndpointDisplacement false)

theorem hillHminusGapWidthDisplacement_gap_difference_bound (q : PeriodOneRealHminusOne)
    (m : ℕ+) (x y : ℝ)
    (hx : x ∈ Icc (hillHminusLabels q.val q.property (2*(m:ℕ)-1))
      (hillHminusLabels q.val q.property (2*(m:ℕ))))
    (hy : y ∈ Icc (hillHminusLabels q.val q.property (2*(m:ℕ)-1))
      (hillHminusLabels q.val q.property (2*(m:ℕ)))) :
    ‖((x:ℂ)-(y:ℂ))/(m:ℕ)‖ ≤ ‖hillHminusGapWidthDisplacement q m‖ := by
  have hb : |x-y| ≤ |hillHminusLabels q.val q.property (2*(m:ℕ))-
      hillHminusLabels q.val q.property (2*(m:ℕ)-1)| := by
    apply abs_le.mpr
    constructor <;> linarith [hx.1,hx.2,hy.1,hy.2,le_abs_self (hillHminusLabels q.val q.property (2*(m:ℕ))-
      hillHminusLabels q.val q.property (2*(m:ℕ)-1))]
  rw [hillHminusGapWidthDisplacement_apply]
  simp only [norm_div,← ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  exact div_le_div_of_nonneg_right hb (norm_nonneg _)

end NLS.KdV
