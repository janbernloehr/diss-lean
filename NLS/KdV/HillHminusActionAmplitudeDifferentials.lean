import NLS.KdV.HillHminusRelativeAmplitude
import NLS.ComplexAnalysis.SquareRootDifferential

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
namespace NLS.KdV

theorem hillRealGapIntegral_pos_of_open (q : RealPeriodOneHillPotential) (n : ℕ+)
    (hgap : hillRealGapHalfLength q.val q.property.1 q.property.2 n ≠ 0) :
    0 < hillRealGapIntegral q.val q.property.1 q.property.2 n 0 := by
  apply (hillRealGapIntegral_pos_iff q.val q.property.1 q.property.2 n n.pos).mpr
  apply lt_of_le_of_ne (monotone_hillRealLabels q.val q.property.1 q.property.2 (by omega))
  intro he
  exact hgap (by simp only [hillRealGapHalfLength,he,sub_self,zero_div])

/-- Original action and positive amplitude germs retain their exact
physical normalization and their ENTIRE H-minus-one differential identity. -/
theorem exists_hillOriginal_action_amplitude_hminus_differentials
    (q : RealPeriodOneHillPotential) (n : ℕ+)
    (hgap : hillRealGapHalfLength q.val q.property.1 q.property.2 n ≠ 0) :
    ∃ J A : PeriodOneHminusOne → ℂ,
      AnalyticAt ℂ J (hillOriginalHminusSource q.val) ∧
      AnalyticAt ℂ A (hillOriginalHminusSource q.val) ∧
      (∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
        J (hillOriginalHminusSource p.val) = (hillRealGapIntegral p.val p.property.1 p.property.2 n 0 : ℂ)) ∧
      (∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
        A (hillOriginalHminusSource p.val) =
          (Real.sqrt (2 * hillRealGapIntegral p.val p.property.1 p.property.2 n 0) : ℂ)) ∧
      A (hillOriginalHminusSource q.val) ≠ 0 ∧
      fderiv ℂ A (hillOriginalHminusSource q.val) =
        (A (hillOriginalHminusSource q.val))⁻¹ • fderiv ℂ J (hillOriginalHminusSource q.val) := by
  let J := hillHminusRelativeAction q.val q.property.1 q.property.2 n
  let A := hillHminusRelativeAmplitude q n
  obtain ⟨U,_,hqU,hJU,_⟩ := exists_hillHminusRelativeAction_analytic_neighborhood
    q.val q.property.1 q.property.2 n n.pos
  have hJ : AnalyticAt ℂ J (hillOriginalHminusSource q.val) := hJU _ hqU
  obtain ⟨V,hV,hqV,hJM⟩ := exists_hillHminusRelativeAction_original_matching q n n.pos
  have hJreal : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      J (hillOriginalHminusSource p.val) = (hillRealGapIntegral p.val p.property.1 p.property.2 n 0 : ℂ) :=
    Filter.Eventually.mono (hV.mem_nhds hqV) (fun p hp => hJM p hp)
  obtain ⟨W,_,hqW,hAW,hAM⟩ :=
    exists_hillHminusRelativeAmplitude_isospectral_physical_germs q n n.pos hgap
  have hA : AnalyticAt ℂ A (hillOriginalHminusSource q.val) := hAW _ hqW
  obtain ⟨T,hT,hqT,hAT⟩ := hAM q (fun _ => rfl)
  have hAreal : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      A (hillOriginalHminusSource p.val) =
        (Real.sqrt (2 * hillRealGapIntegral p.val p.property.1 p.property.2 n 0) : ℂ) :=
    Filter.Eventually.mono (hT.mem_nhds hqT) (fun p hp => hAT p hp)
  have hne : A (hillOriginalHminusSource q.val) ≠ 0 := by
    rw [hAreal.self_of_nhds]
    exact ofReal_ne_zero.mpr (Real.sqrt_pos.mpr
      (mul_pos (by norm_num) (hillRealGapIntegral_pos_of_open q n hgap))).ne'
  refine ⟨J,A,hJ,hA,hJreal,hAreal,hne,?_⟩
  exact fderiv_squareRoot_twice_of_sq_eq A J _ hA hJ
    (Filter.Eventually.of_forall (fun a => complex_sqrt_sq (2 * J a))) hne

end NLS.KdV
