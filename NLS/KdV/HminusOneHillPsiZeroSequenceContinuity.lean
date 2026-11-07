import NLS.KdV.HillPositiveEndpointSequenceContinuity
import NLS.KdV.HminusOneHillPsiRealZeroContinuity
import NLS.KdV.HminusOneHillPsiZeroAsymptotics

/-! Coordinate-continuous selections in the full original real gaps
are continuous as entire inverse-index l2 sequences. In particular this
holds for the actual indexed Hill zeros, including the omitted midpoint.
Complex Banach sequence analyticity and fine estimates are not inferred. -/
noncomputable section
open Set Complex Filter Topology
open scoped ENNReal Classical
namespace NLS.KdV

def hillHminusGapSampleDisplacement
    (σ : {a : PeriodOneHminusOne // IsRealPeriodOneHminusOne a} → ℕ+ → ℝ)
    (hσ : ∀ q (m : ℕ+), σ q m ∈ Icc (hillHminusLabels q.val q.property (2*(m:ℕ)-1))
      (hillHminusLabels q.val q.property (2*(m:ℕ))))
    (q : {a : PeriodOneHminusOne // IsRealPeriodOneHminusOne a}) : lp (fun _ : ℕ+ => ℂ) 2 :=
  ⟨fun m => ((σ q m:ℂ)-((Real.pi:ℂ)*(m:ℕ))^2)/(m:ℕ),
    hillHminusOriginal_real_gap_samples_inverseIndex_error q.val q.property (σ q) (hσ q)⟩

theorem continuous_hillHminusGapSampleDisplacement
    (σ : {a : PeriodOneHminusOne // IsRealPeriodOneHminusOne a} → ℕ+ → ℝ)
    (hσ : ∀ q (m : ℕ+), σ q m ∈ Icc (hillHminusLabels q.val q.property (2*(m:ℕ)-1))
      (hillHminusLabels q.val q.property (2*(m:ℕ))))
    (hcont : ∀ m, Continuous (fun q => σ q m)) :
    Continuous (hillHminusGapSampleDisplacement σ hσ) := by
  let g := fun q => LpSequence.magnitude (hillHminusPositiveEndpointDisplacement false q)+
    LpSequence.magnitude (hillHminusPositiveEndpointDisplacement true q)
  have hg : Continuous g :=
    (LpSequence.continuous_magnitude.comp (continuous_hillHminusPositiveEndpointDisplacement false)).add
      (LpSequence.continuous_magnitude.comp (continuous_hillHminusPositiveEndpointDisplacement true))
  apply continuous_iff_continuousAt.mpr
  intro q
  refine LpSequence.continuousAt_of_coordinates_of_continuous_majorant (by norm_num)
    (hillHminusGapSampleDisplacement σ hσ) g q ?_ hg.continuousAt ?_
  · intro m
    change ContinuousAt (fun a => ((σ a m:ℂ)-((Real.pi:ℂ)*(m:ℕ))^2)/(m:ℕ)) q
    exact ((Complex.continuous_ofReal.comp (hcont m)).sub continuous_const).div_const _ |>.continuousAt
  · apply Eventually.of_forall
    intro a m
    let l := hillHminusLabels a.val a.property (2*(m:ℕ)-1)
    let r := hillHminusLabels a.val a.property (2*(m:ℕ))
    let y : ℝ := (Real.pi*(m:ℝ))^2
    have hx : σ a m ∈ Icc l r := hσ a m
    have hb : |σ a m-y| ≤ |l-y|+|r-y| := by
      apply abs_le.mpr
      constructor
      · linarith [neg_abs_le (l-y),abs_nonneg (r-y),hx.1]
      · linarith [le_abs_self (r-y),abs_nonneg (l-y),hx.2]
    have hy : ((Real.pi:ℂ)*(m:ℕ))^2 = (y:ℂ) := by simp only [y,ofReal_pow,ofReal_mul,ofReal_natCast]
    have hgval : ‖g a m‖ = ‖((l:ℂ)-((Real.pi:ℂ)*(m:ℕ))^2)/(m:ℕ)‖+
        ‖((r:ℂ)-((Real.pi:ℂ)*(m:ℕ))^2)/(m:ℕ)‖ := by
      change ‖(‖((l:ℂ)-((Real.pi:ℂ)*(m:ℕ))^2)/(m:ℕ)‖:ℂ)+
        (‖((r:ℂ)-((Real.pi:ℂ)*(m:ℕ))^2)/(m:ℕ)‖:ℂ)‖ = _
      rw [← Complex.ofReal_add,Complex.norm_real,Real.norm_of_nonneg (by positivity)]
    rw [hgval]
    change ‖((σ a m:ℂ)-((Real.pi:ℂ)*(m:ℕ))^2)/(m:ℕ)‖ ≤ _
    simp only [hy,norm_div,← ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
    rw [← add_div]
    exact div_le_div_of_nonneg_right hb (norm_nonneg _)

def hillHminusPsiZeroDisplacement (n : ℕ+)
    (q : {a : PeriodOneHminusOne // IsRealPeriodOneHminusOne a}) : lp (fun _ : ℕ+ => ℂ) 2 :=
  hillHminusGapSampleDisplacement (fun a m => hillHminusCanonicalPsiRealZero n m a.val a.property)
    (fun a m => hillHminusCanonicalPsiRealZero_mem_gap n m a.val a.property) q

theorem hillHminusPsiZeroDisplacement_apply (n m : ℕ+)
    (q : {a : PeriodOneHminusOne // IsRealPeriodOneHminusOne a}) :
    hillHminusPsiZeroDisplacement n q m = ((hillHminusCanonicalPsiRealZero n m q.val q.property:ℂ)-
      ((Real.pi:ℂ)*(m:ℕ))^2)/(m:ℕ) := rfl

theorem continuous_hillHminusPsiZeroDisplacement (n : ℕ+) :
    Continuous (hillHminusPsiZeroDisplacement n) :=
  continuous_hillHminusGapSampleDisplacement
    (fun a m => hillHminusCanonicalPsiRealZero n m a.val a.property)
    (fun a m => hillHminusCanonicalPsiRealZero_mem_gap n m a.val a.property)
    (fun m => continuous_hillHminusCanonicalPsiRealZero n m)

end NLS.KdV
