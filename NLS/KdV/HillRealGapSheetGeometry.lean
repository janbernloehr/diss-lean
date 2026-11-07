import NLS.KdV.HillOnIndexRightSimpleEndpoint
import NLS.KdV.HillDirichletSpectralTerminalVelocity

/-! Actual native geometry of every real indexed periodic gap.
Consecutive spectral labels exclude interior radicand zeros, and both
endpoints of an open original gap are simple native radicand zeros. -/
noncomputable section
open Set Complex NLS.ComplexAnalysis
namespace NLS.KdV

theorem hillHminusRadicand_zero_in_gap_iff_endpoint (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (n : ℕ+) (y : ℝ)
    (hy : y ∈ Icc (hillHminusLabels q hr (2*(n:ℕ)-1)) (hillHminusLabels q hr (2*(n:ℕ)))) :
    hillHminusRadicand q (y:ℂ)=0 ↔
      y=hillHminusLabels q hr (2*(n:ℕ)-1) ∨ y=hillHminusLabels q hr (2*(n:ℕ)) := by
  constructor
  · intro hz
    obtain ⟨j,hj⟩ := (hillHminusLabels_roots_iff q hr (y:ℂ)).mp hz
    have he : y=hillHminusLabels q hr j := ofReal_inj.mp hj
    by_cases hleft : j ≤ 2*(n:ℕ)-1
    · exact Or.inl (le_antisymm (he ▸ monotone_hillHminusLabels q hr hleft) hy.1)
    · have hright : 2*(n:ℕ) ≤ j := by omega
      exact Or.inr (le_antisymm hy.2 (he ▸ monotone_hillHminusLabels q hr hright))
  · rintro (rfl | rfl) <;> exact (hillHminusLabels_roots_iff q hr _).mpr ⟨_,rfl⟩

theorem hillHminusRadicand_deriv_at_open_gap_endpoints_ne_zero (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (n : ℕ+) (hgap : hillHminusCanonicalGapSquare n q ≠ 0) :
    deriv (hillHminusRadicand q) (hillHminusLabels q hr (2*(n:ℕ)-1):ℂ) ≠ 0 ∧
      deriv (hillHminusRadicand q) (hillHminusLabels q hr (2*(n:ℕ)):ℂ) ≠ 0 := by
  obtain ⟨P,hq,_⟩ := exists_hillProductEquationPatch q hr
  exact ⟨P.native_radicand_deriv_at_real_open_gap_left_ne_zero n q hq hr hgap,
    P.native_radicand_deriv_at_real_open_gap_right_ne_zero n q hq hr hgap⟩

theorem analyticOnNhd_hillHminusDiscriminant_energy (q : PeriodOneHminusOne) :
    AnalyticOnNhd ℂ (hillHminusDiscriminant q) univ := by
  intro E _
  exact (analyticOnNhd_hillHminusDiscriminant_joint (E,q) (mem_univ _)).comp
    (f := fun z : ℂ => (z,q)) (analyticAt_id.prod analyticAt_const)

theorem continuous_deriv_hillHminusDiscriminant (q : PeriodOneHminusOne) :
    Continuous (deriv (hillHminusDiscriminant q)) := by
  have hc := analyticOnNhd_hillHminusDiscriminantEnergyDerivative_joint.continuous.comp
    (continuous_id.prodMk (continuous_const : Continuous (fun _ : ℂ => q)))
  simpa only [Function.comp_def,id_eq] using! hc

theorem deriv_hillHminusRadicand (q : PeriodOneHminusOne) (E : ℂ) :
    deriv (hillHminusRadicand q) E=
      2*hillHminusDiscriminant q E*deriv (hillHminusDiscriminant q) E := by
  have hd := ((analyticOnNhd_hillHminusDiscriminant_energy q E (mem_univ _)).differentiableAt.hasDerivAt.pow 2).sub_const 4
  change HasDerivAt (hillHminusRadicand q) _ E at hd
  simpa only [show (2:ℕ)-1=1 by decide,pow_one,Nat.cast_ofNat] using hd.deriv

theorem hillHminusDiscriminant_energy_derivative_im_eq_zero (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (E : ℝ) :
    (deriv (hillHminusDiscriminant q) (E:ℂ)).im=0 :=
  deriv_im_eq_zero_of_real_axis _ (fun z => (analyticOnNhd_hillHminusDiscriminant_energy q z (mem_univ _)).differentiableAt)
    (hillHminusDiscriminant_im_eq_zero_of_real q hr) E

end NLS.KdV
