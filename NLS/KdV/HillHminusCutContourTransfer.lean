import NLS.KdV.HillHminusIntrinsicPeriods

/-! # Weighted physical energy contours on the original cut domain

The contour transfer only requires a coefficient analytic near the
actual cut complement. This includes powers of the shifted physical
primitive, even though those powers need not be entire in energy.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate
namespace NLS.KdV.HillHminusPsiChart

/-- Every coefficient analytic on the original cut domain has the same original physical period on
the actual quadratic energy contour and the fixed intrinsic Hill circle. -/
theorem energy_contour_integral_eq_intrinsic_circle_of_cut_analytic (P : HillHminusPsiChart)
    (q : RealPeriodOneHillPotential) (hq : hillOriginalHminusSource q.val∈P.source)
    (hreal : ∀ a∈P.miura.domain, IsRealPeriodOneHminusOne a → ∀ k : ℤ,
      P.miura.lift a (-k)=conj (P.miura.lift a k))
    (houtside : hillHminusRadicand (hillOriginalHminusSource q.val) (-P.miura.energyShift)≠0)
    (c : ℝ) (hshift : P.miura.energyShift=(c:ℂ)^2) (m : ℕ+)
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num)
      (hillMiuraDiagonal (P.miura.lift (hillOriginalHminusSource q.val))) ((m:ℕ):ℤ))
    (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F (hillL2RealCutDomain q.val q.property.1 q.property.2)) :
    (quadraticEnergyLoop (PiecewiseC1Loop.circle (D.center:ℂ) D.radius)
      P.miura.energyShift).integral (fun E => F E/
        hillEnergyCanonicalRootProduct q.val q.property.1 q.property.2 E)=
      ∮ E in C((hillRealGapCenter q.val q.property.1 q.property.2 m:ℂ),
        hillRealGapHalfLength q.val q.property.1 q.property.2 m+
          hillRealGapCollar q.val q.property.1 q.property.2 m),
        F E/hillEnergyCanonicalRootProduct q.val q.property.1 q.property.2 E := by
  let u : PeriodOneRealL2 := ⟨P.miura.lift (hillOriginalHminusSource q.val),
    hreal _ hq.1 (hillOriginalHminusSource_real q.val q.property.2)⟩
  have hpos := miuraPeriodCircle_left_pos u m D
  obtain ⟨hleft,hright⟩ := P.energy_contour_endpoints_in_original_bands q hq hreal houtside c hshift m D
  obtain ⟨hrefleft,hrefright⟩ := hillIntrinsicCircle_endpoints_in_bands q m
  obtain ⟨hd,hη,_⟩ := hillRealGapContour_geometry q.val q.property.1 q.property.2 m m.pos
  rw [hshift,←ofReal_pow]
  apply integral_quadraticEnergyCircle_eq_circleIntegral D.center D.radius (c^2) _ _
    (hillRealLabels q.val q.property.1 q.property.2 (2*(m:ℕ)-2))
    (hillRealLabels q.val q.property.1 q.property.2 (2*(m:ℕ)-1))
    (hillRealLabels q.val q.property.1 q.property.2 (2*(m:ℕ)))
    (hillRealLabels q.val q.property.1 q.property.2 (2*(m:ℕ)+1))
    (hillL2RealCutDomain q.val q.property.1 q.property.2) _
    D.radius_pos (by linarith) (by linarith) hleft hright hrefleft hrefright
  · rintro E (hi | hl | hr)
    · exact Or.inl hi
    · refine Or.inr ⟨(m:ℕ)-1,?_⟩
      rw [show 2*((m:ℕ)-1)+1=2*(m:ℕ)-1 by have := m.pos; omega,
        show 2*((m:ℕ)-1)=2*(m:ℕ)-2 by have := m.pos; omega]
      exact hl
    · exact Or.inr ⟨(m:ℕ),hr⟩
  · intro E hE
    exact ((hF E hE).div
      (analyticOnNhd_hillEnergyCanonicalRootProduct q.val q.property.1 q.property.2 E hE)
      (hillEnergyCanonicalRootProduct_ne_zero_on_realCutDomain q.val q.property.1 q.property.2 E hE)).differentiableAt

end NLS.KdV.HillHminusPsiChart
