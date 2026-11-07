import NLS.Articles.KdVKdV2Frequencies.DiagonalFrequencyPairCharts
import NLS.Articles.KdVKdV2Frequencies.WeightedPairDiscriminant
import NLS.KdV.PhysicalMomentIsospectral
import NLS.KdV.ClassicalPeriodOperator
import NLS.SequenceSpaces.RealActionNormalizedInvariance

/-! The actual finite-exponent diagonal symbol is invariant on all
real action fibers, including closed selected actions. The closed case
uses simultaneous real opening and actual rough Arnold calibration. -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.KdV NLS.ZakharovShabat
open NLS.Articles.KdVConvexity
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies.DiagonalFrequencyPairChart
variable {D : GlobalRoughAbelianForwardData} {I : PeriodOneHminusOne → BaseActionSpace} {t : ℝ}

theorem action_scaled_symbol_identity
    (P : DiagonalFrequencyPairChart D I t)
    (Ω : Set PeriodOneHminusOne) (hΩ : {q | IsRealPeriodOneHminusOne q}⊆Ω)
    (hI : AnalyticOnNhd ℂ I Ω)
    (hrec : ∀ q (hr : IsRealPeriodOneHminusOne q) (n : ℕ+),
      (I q).val (actionIndexEquiv.symm n)=hillHminusRealGapContourMoment q hr n 0)
    (z : Coeff 2 × Coeff 2) (hz : z∈P.domain) (hzr : z∈Coeff.realPairLocus 2) (k : ℤ) :
    quadraticActionsExponent (q := 1) z k*P.packet z (actionIndexEquiv k : ℤ)=
      ((Weight.sobolev (2*t-1) (actionIndexEquiv k : ℤ) : ℂ)/6)*
        (P.physicalChart.correction (actionIndexEquiv k) (P.roughPotential z)+6*(I (P.roughPotential z)).val k-
          P.physicalChart.offDiagonalCorrection (actionIndexEquiv k) (P.roughPotential z)) := by
  have hQ := Arnold_action_of_weighted_pair_inverse_identity D Ω hΩ I hI hrec t
    (P.roughPotential z) (P.rough_real z hz hzr) z hzr (P.rough_signed z hz hzr) k
  have hf := P.factor z hz hzr (actionIndexEquiv k)
  simp only [Equiv.symm_apply_apply] at hf
  rw [←hQ]
  linear_combination -((Weight.sobolev (2*t-1) (actionIndexEquiv k : ℤ) : ℂ)/6)*hf

theorem packet_eq_of_real_actions
    (P : DiagonalFrequencyPairChart D I t)
    (Ω : Set PeriodOneHminusOne) (hΩ : {q | IsRealPeriodOneHminusOne q}⊆Ω)
    (hI : AnalyticOnNhd ℂ I Ω)
    (hrec : ∀ q (hr : IsRealPeriodOneHminusOne q) (n : ℕ+),
      (I q).val (actionIndexEquiv.symm n)=hillHminusRealGapContourMoment q hr n 0)
    (z : Coeff 2 × Coeff 2) (hz : z∈P.domain) (w : Coeff 2 × Coeff 2) (hw : w∈P.domain)
    (hzr : z∈Coeff.realPairLocus 2) (hwr : w∈Coeff.realPairLocus 2)
    (ha : quadraticActionsExponent (q := 1) w=quadraticActionsExponent z) : P.packet w=P.packet z := by
  have hcoord (k : ℤ) : P.packet w (actionIndexEquiv k : ℤ)=P.packet z (actionIndexEquiv k : ℤ) := by
    let f := fun x => P.packet x (actionIndexEquiv k : ℤ)
    let G := fun x => ((Weight.sobolev (2*t-1) (actionIndexEquiv k : ℤ) : ℂ)/6)*
      (P.physicalChart.correction (actionIndexEquiv k) (P.roughPotential x)+6*(I (P.roughPotential x)).val k-
        P.physicalChart.offDiagonalCorrection (actionIndexEquiv k) (P.roughPotential x))
    have hfa : AnalyticOnNhd ℂ f P.domain := fun x hx =>
      ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 (actionIndexEquiv k : ℤ)).analyticAt _).comp
        (P.analytic_packet x hx)
    have hf : ContinuousOn f P.domain := hfa.continuousOn
    apply Coeff.eq_on_real_action_fibers_of_normalized_invariant P.domain P.domain_open k f G hf ?_
      (fun x hx hxr => P.action_scaled_symbol_identity Ω hΩ hI hrec x hx hxr k)
      z hz hzr w hw hwr ha
    intro x hx y hy hxr hyr hxy
    have hrx := P.rough_real x hx hxr
    have hry := P.rough_real y hy hyr
    have hD : hillHminusDiscriminant (P.roughPotential y)=hillHminusDiscriminant (P.roughPotential x) :=
      (discriminant_eq_of_weighted_pair_actions D t (P.roughPotential x) (P.roughPotential y)
        hrx hry (P.rough_zero x hx) (P.rough_zero y hy) x y
        (P.rough_signed x hx hxr) (P.rough_signed y hy hyr) hxy).symm
    have hIy : (I (P.roughPotential y)).val k=(I (P.roughPotential x)).val k := by
      have hyI := hrec (P.roughPotential y) hry (actionIndexEquiv k)
      have hxI := hrec (P.roughPotential x) hrx (actionIndexEquiv k)
      simp only [Equiv.symm_apply_apply] at hyI hxI
      exact hyI.trans (((hillHminusRealGapContourMoments_eq_of_discriminant_eq
        (P.roughPotential y) (P.roughPotential x) hry hrx hD (actionIndexEquiv k)).1 0).trans hxI.symm)
    have hc := P.physicalChart.correction_eq_of_discriminant_eq
      (P.roughPotential x) (P.roughPotential y) (P.rough_mem x hx) (P.rough_mem y hy) hrx hry hD (actionIndexEquiv k)
    have ho := P.physicalChart.offDiagonalCorrection_eq_of_discriminant_eq
      (P.roughPotential x) (P.roughPotential y) (P.rough_mem x hx) (P.rough_mem y hy) hrx hry hD (actionIndexEquiv k)
    change ((Weight.sobolev (2*t-1) (actionIndexEquiv k : ℤ) : ℂ)/6)*_= _
    rw [hc,ho,hIy]
  ext j
  by_cases hj : 0<j
  · let n := positiveIntegerIndex j hj
    have hnj : (n : ℤ)=j := positiveIntegerIndex_int j hj
    have hh := hcoord (actionIndexEquiv.symm n)
    rw [Equiv.apply_symm_apply,hnj] at hh
    exact hh
  · rw [P.nonpositive w hw j (by omega),P.nonpositive z hz j (by omega)]

end NLS.Articles.KdVKdV2Frequencies.DiagonalFrequencyPairChart
