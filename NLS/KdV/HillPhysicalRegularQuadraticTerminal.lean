import NLS.KdV.HillPhysicalQuadraticTerminal

/-! # Physical quadratic terminal matching including the own mode

The Kronecker term in the differential equation cancels exactly against
the linear part of the regular Abelian primitive. Collapsed gaps are included.
-/

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



theorem hillRegularAbelianCorrection_eq_regular_quadratic_terminal
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (c : ℂ) (R : ℝ) (hR : 0 < R) (J : ℂ → ℂ)
    (hJ : AnalyticOnNhd ℂ J (ball c (3*R/4)))
    (hτ : ‖(hillRealGapCenter q hq hr k : ℂ)-c‖ ≤ R/16)
    (hδ : ‖(hillRealGapHalfLength q hq hr k : ℂ)‖ ≤ R/16)
    (heq : ∀ E ∈ ball c (3*R/4),
      ((E-(hillRealGapCenter q hq hr k : ℂ))^2-(hillRealGapHalfLength q hq hr k : ℂ)^2)*deriv J E+
        (E-(hillRealGapCenter q hq hr k : ℂ))*J E=
          -I*hillAbelianSelectedGlobalPsi q hq hr n hn E/hillDeflatedEnergyCanonicalRoot q hq hr k E - (if k=n then 1 else 0)) :
    hillRegularAbelianCorrection q hq hr n hn k hk=
      I*hillDirichletSheetRoot (SpectralWeight.one.toCoeff q) (hillDirichletEnergy q hq hr k hk)/
        hillDeflatedEnergyCanonicalRoot q hq hr k (hillDirichletEnergy q hq hr k hk)*
          J (hillDirichletEnergy q hq hr k hk) := by
  by_cases hgap : hillRealGapHalfLength q hq hr k=0
  · have hc : hillRealLabels q hq hr (2*k-1)=hillRealLabels q hq hr (2*k) := by
      have hh := hgap
      dsimp only [hillRealGapHalfLength] at hh
      linarith
    rw [hillRegularAbelianCorrection_closed q hq hr n hn k hk hgap,
      hillDirichletSheetRoot_at_dirichlet_eq_norming q hq hr k hk,
      hillDirichletLogMultiplier_eq_zero_of_closed_gap q hq hr k hk hc]
    simp
  · let τ : ℂ := hillRealGapCenter q hq hr k
    let δ : ℂ := hillRealGapHalfLength q hq hr k
    let Q : ℂ → ℂ := fun w => J (τ+w)
    have hpoint (w : ℂ) (hw : w ∈ ball (0 : ℂ) (R/4)) : τ+w ∈ ball c (3*R/4) := by
      have hw' : ‖w‖ < R/4 := by simpa only [mem_ball,dist_zero_right] using hw
      have hh : ‖τ+w-c‖ ≤ ‖τ-c‖+‖w‖ := by
        rw [show τ+w-c=(τ-c)+w by ring]
        exact norm_add_le _ _
      rw [mem_ball,dist_eq_norm]
      linarith
    have hQ : AnalyticOnNhd ℂ Q (ball (0 : ℂ) (R/4)) := by
      intro w hw
      exact (hJ (τ+w) (hpoint w hw)).comp (f := fun z : ℂ => τ+z) (analyticAt_const.add analyticAt_id)
    have hder (w : ℂ) (hw : w ∈ ball (0 : ℂ) (R/4)) : deriv Q w=deriv J (τ+w) := by
      have hh := ((hJ (τ+w) (hpoint w hw)).differentiableAt.hasDerivAt.comp w ((hasDerivAt_id w).const_add τ)).deriv
      simpa only [Q,id_eq,mul_one,Function.comp_def] using hh
    have hODE (w : ℂ) (hw : w ∈ ball (0 : ℂ) (R/4)) :
        (w^2-δ^2)*deriv Q w+w*Q w =
          -I*hillAbelianSelectedGlobalPsi q hq hr n hn (τ+w)/hillDeflatedEnergyCanonicalRoot q hq hr k (τ+w)-(if k=n then 1 else 0) := by
      have hh := heq (τ+w) (hpoint w hw)
      rw [hder w hw]
      simpa only [Q,τ,δ,add_sub_cancel_left] using hh
    let θ := hillDirichletSelectedRealAngle q hq hr k hk hgap
    have hspec := hillDirichletSelectedRealAngle_spec q hq hr k hk hgap
    have hcos := hillAbelianCosinePrimitive_eq_linear_add_quadratic q hq hr n k hn hk Q (R/4)
      (by linarith : ‖(hillRealGapHalfLength q hq hr k : ℂ)‖ < R/4) hQ hODE θ
    have harg : τ+cosineGapPoint 0 δ (θ : ℂ)=(hillDirichletEnergy q hq hr k hk : ℂ) := by
      simpa only [τ,δ,cosineGapPoint,zero_add] using hspec.2.1
    rw [hillRegularAbelianCorrection,dif_neg hgap,hillRegularAbelianPrimitive,hcos]
    simp only [regularQuadraticCosinePrimitive]
    change (if k=n then (1:ℂ) else 0)*((θ:ℂ)-(Real.pi:ℂ)) +
      δ*Complex.sin (θ : ℂ)*J (τ+cosineGapPoint 0 δ (θ : ℂ)) -
      (if k=n then (1:ℂ) else 0)*((θ:ℂ)-(Real.pi:ℂ)) = _
    rw [add_sub_cancel_left]
    rw [harg,hspec.2.2,hillDirichletGapSine]
    have hδn : δ≠0 := ofReal_ne_zero.mpr hgap
    by_cases hUn : hillDeflatedEnergyCanonicalRoot q hq hr k (hillDirichletEnergy q hq hr k hk)=0
    · simp only [hUn,mul_zero,div_zero,mul_zero]
    · dsimp only [δ]
      field_simp [hgap,hUn]

end NLS.KdV
