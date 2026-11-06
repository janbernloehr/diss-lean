import NLS.KdV.HillDirichletAnalyticCircleData
import NLS.ComplexAnalysis.ParametricTrigonometricTerminal

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

theorem hillDirichlet_angle_im_eq_zero (k : ℕ) (hk : 1 ≤ k)
    (hgap : hillRealGapHalfLength q hq hr k ≠ 0) (e : ℂ)
    (hpoint : cosineGapPoint (hillRealGapCenter q hq hr k) (hillRealGapHalfLength q hq hr k) e =
      (hillDirichletEnergy q hq hr k hk : ℂ))
    (hsin : Complex.sin e = hillDirichletGapSine q hq hr k hk) : e.im = 0 := by
  obtain ⟨f,hf,hfpoint,hfcos,hfsin⟩ := exists_hillDirichlet_terminal_angle q hq hr k hk hgap
  have hecos : Complex.cos e = hillDirichletGapCosine q hq hr k hk := by
    apply (eq_div_iff (ofReal_ne_zero.mpr hgap)).mpr
    dsimp only [cosineGapPoint] at hpoint
    linear_combination hpoint
  obtain ⟨j,hj⟩ := eq_mod_two_pi_of_cos_eq_of_sin_eq e f (hecos.trans hfcos.symm) (hsin.trans hfsin.symm)
  rw [hj]
  have hfi : f.im = 0 := im_eq_zero_of_mem_real_segment (-Real.pi) Real.pi f (by simpa using hf)
  simp [hfi]

theorem exists_hillDirichlet_analytic_sheeted_angle (k : ℕ) (hk : 1 ≤ k)
    (hgap : hillRealGapHalfLength q hq hr k ≠ 0) :
    ∃ ε : Coeff 2 → ℂ, ∃ e : ℂ,
      AnalyticAt ℂ ε (SpectralWeight.one.toCoeff q) ∧ ε (SpectralWeight.one.toCoeff q) = e ∧
      e ∈ segment ℝ (-(Real.pi : ℂ)) (Real.pi : ℂ) ∧
      ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
        hillRealGapHalfLength p.val p.property.1 p.property.2 k ≠ 0 ∧
        (ε (SpectralWeight.one.toCoeff p.val)).im = 0 ∧
        cosineGapPoint (hillRealGapCenter p.val p.property.1 p.property.2 k)
          (hillRealGapHalfLength p.val p.property.1 p.property.2 k) (ε (SpectralWeight.one.toCoeff p.val)) =
            (hillDirichletEnergy p.val p.property.1 p.property.2 k hk : ℂ) ∧
        Complex.sin (ε (SpectralWeight.one.toCoeff p.val)) = hillDirichletGapSine p.val p.property.1 p.property.2 k hk := by
  obtain ⟨d,μ,S,hd,hμ,hS,hd0,hμ0,hS0,hcircle,hphysical⟩ :=
    exists_hillDirichlet_analytic_circle_data q hq hr k hk hgap
  obtain ⟨U,_,hqU,hM,_,_⟩ := exists_hillLocalGapSymmetricData_analytic_neighborhood q hq hr k hk
  have hM0 := (hillLocalGapSymmetricData_eq_physical_of_geometry q hq hr q hq hr k hk
    (hillRealGapContour_band_bounds q hq hr k hk)
    (hillRealGapSegment_subset_intrinsic_contour_ball q hq hr k hk)).1
  obtain ⟨e,he,hpoint,_,hsin⟩ := exists_hillDirichlet_terminal_angle q hq hr k hk hgap
  obtain ⟨ε,hε,hε0,hterminal⟩ := exists_analytic_parametricCosine_terminal_with_sine
    (hillLocalGapMidpoint q hq hr k) d μ S (SpectralWeight.one.toCoeff q) e
    (hM _ hqU) hd hμ hS (hd0 ▸ ofReal_ne_zero.mpr hgap) (hS0.trans hsin.symm)
    (by rw [hM0,hd0,hμ0];exact hpoint) hcircle
  let P : RealPeriodOneHillPotential → Coeff 2 := fun p => SpectralWeight.one.toCoeff p.val
  have hP : Continuous P := SpectralWeight.one.toCoeff.continuous.comp continuous_subtype_val
  refine ⟨ε,e,hε,hε0,he,?_⟩
  filter_upwards [hphysical,hP.continuousAt.tendsto.eventually hterminal] with p hp ht
  have hpointp : cosineGapPoint (hillRealGapCenter p.val p.property.1 p.property.2 k)
      (hillRealGapHalfLength p.val p.property.1 p.property.2 k) (ε (P p)) =
        (hillDirichletEnergy p.val p.property.1 p.property.2 k hk : ℂ) := by
    rw [← hp.2.2.2.2,← hp.2.1]
    exact ht.1.trans hp.2.2.1
  have hsinp : Complex.sin (ε (P p)) = hillDirichletGapSine p.val p.property.1 p.property.2 k hk :=
    ht.2.trans hp.2.2.2.1
  exact ⟨hp.1,hillDirichlet_angle_im_eq_zero p.val p.property.1 p.property.2 k hk hp.1 _ hpointp hsinp,hpointp,hsinp⟩

end NLS.KdV
