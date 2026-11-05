import NLS.KdV.HillHminusOriginalSheets
import NLS.KdV.HillHminusOneBoundaryAction
import NLS.KdV.HillL2GlobalGapBoundaryValues

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
namespace NLS.KdV

/-- Uniqueness of the actual upper primitive boundary limit identifies
the native filled-square root with the ORIGINAL signed arcosh profile. -/
theorem hillHminusGapSquare_sqrt_eq_original_profile
    (q : RealPeriodOneHillPotential) (n : ℕ+) (r : ℝ) (V : Set PeriodOneHminusOne)
    (K : ℂ × PeriodOneHminusOne → ℂ)
    (hK : AnalyticOnNhd ℂ K (hillHminusGapSquareDisc n r ×ˢ V))
    (hmatch : ∀ t ∈ (hillHminusGapSquareDisc n r ×ˢ V) ∩ hillHminusContinuationDomain,
      K t=(hillHminusContinuedPrimitive t+I*(n : ℂ)*Real.pi)^2)
    (hqV : hillOriginalHminusSource q.val∈V) (x : ℝ)
    (hx : x∈Icc (hillRealLabels q.val q.property.1 q.property.2 (2*(n : ℕ)-1))
      (hillRealLabels q.val q.property.1 q.property.2 (2*(n : ℕ))))
    (hdisc : (x : ℂ)∈ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r))
    (hcont : ContinuousAt Complex.sqrt (K ((x : ℂ),hillOriginalHminusSource q.val))) :
    Complex.sqrt (K ((x : ℂ),hillOriginalHminusSource q.val))=
      (hillRealGapProfile (SpectralWeight.one.toCoeff q.val) n x : ℂ) := by
  have hH := (tendsto_hillHminusShiftedPrimitive_sqrt_boundaries n r V K hK hmatch
    (hillOriginalHminusSource q.val) hqV (hillOriginalHminusSource_real q.val q.property.2)
    x hdisc hcont).1
  have hy : Tendsto (fun y : ℝ => (x : ℂ)+(y : ℂ)*I) (𝓝[>] 0)
      (𝓝[{z : ℂ | 0<z.im}] (x : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : ContinuousAt (fun y : ℝ => (x : ℂ)+(y : ℂ)*I) 0 := by fun_prop
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with y hy
      simpa using hy
  have hL : Tendsto (fun y : ℝ => hillL2ContinuedPrimitive
      ((x : ℂ)+(y : ℂ)*I,SpectralWeight.one.toCoeff q.val)+I*(n : ℂ)*Real.pi)
      (𝓝[>] 0) (𝓝 (hillRealGapProfile (SpectralWeight.one.toCoeff q.val) n x : ℂ)) := by
    simpa only [sub_add_cancel,Function.comp_def] using
      ((tendsto_hillL2ContinuedPrimitive_gap_upper q.val q.property.1 q.property.2 n n.property x hx).comp hy).add_const
        (I*(n : ℂ)*Real.pi)
  have he : (fun y : ℝ => hillHminusContinuedPrimitive
      ((x : ℂ)+(y : ℂ)*I,hillOriginalHminusSource q.val)+I*(n : ℂ)*Real.pi)
      =ᶠ[𝓝[>] 0] (fun y : ℝ => hillL2ContinuedPrimitive
        ((x : ℂ)+(y : ℂ)*I,SpectralWeight.one.toCoeff q.val)+I*(n : ℂ)*Real.pi) := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hne : ((x : ℂ)+(y : ℂ)*I).im≠0 := by simpa using (show y≠0 from ne_of_gt hy)
    rw [hillHminusContinuedPrimitive_original_source_agreement q.val q.property.1 _
      (mem_hillL2ContinuationDomain_of_im_ne_zero q.val q.property.1 q.property.2 _ hne)]
  exact tendsto_nhds_unique hH (hL.congr' he.symm)

/-- The native boundary action is EXACTLY the original real-gap action,
with its two-over-pi factor unchanged, also for a collapsed gap. -/
theorem hillHminusGapBoundaryAction_eq_original_action
    (q : RealPeriodOneHillPotential) (n : ℕ+) (r epsilon : ℝ)
    (hr : 0<r) (hepsilon : epsilon<1) (V : Set PeriodOneHminusOne)
    (K : ℂ × PeriodOneHminusOne → ℂ)
    (hK : AnalyticOnNhd ℂ K (hillHminusGapSquareDisc n r ×ˢ V))
    (hmatch : ∀ t ∈ (hillHminusGapSquareDisc n r ×ˢ V) ∩ hillHminusContinuationDomain,
      K t=(hillHminusContinuedPrimitive t+I*(n : ℂ)*Real.pi)^2)
    (hqV : hillOriginalHminusSource q.val∈V)
    (hpair : HillHminusHighGapPair (hillOriginalHminusSource q.val) n r
      (hillRealLabels q.val q.property.1 q.property.2 (2*(n : ℕ)-1))
      (hillRealLabels q.val q.property.1 q.property.2 (2*(n : ℕ))))
    (hf : ∀ z∈ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r),
      K (z,hillOriginalHminusSource q.val)= -hillHminusGapPolynomial n r (z,hillOriginalHminusSource q.val)*
        hillHminusJointNormalizedGapRoot n r K (z,hillOriginalHminusSource q.val)^2 /
          (4*((Real.pi : ℂ)*(n : ℕ))^2))
    (hnorm : ∀ z∈ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r),
      ‖hillHminusJointNormalizedGapRoot n r K (z,hillOriginalHminusSource q.val)-1‖≤epsilon) :
    hillHminusGapBoundaryAction K (hillOriginalHminusSource q.val)
      (hillRealLabels q.val q.property.1 q.property.2 (2*(n : ℕ)-1))
      (hillRealLabels q.val q.property.1 q.property.2 (2*(n : ℕ)))=
      (hillRealGapIntegral q.val q.property.1 q.property.2 n 0 : ℂ) := by
  have hle := monotone_hillRealLabels q.val q.property.1 q.property.2
    (show 2*(n : ℕ)-1≤2*(n : ℕ) by omega)
  have he (x : ℝ) (hx : x∈Icc
      (hillRealLabels q.val q.property.1 q.property.2 (2*(n : ℕ)-1))
      (hillRealLabels q.val q.property.1 q.property.2 (2*(n : ℕ)))) :
      Complex.sqrt (K ((x : ℂ),hillOriginalHminusSource q.val))=
        (hillRealGapProfile (SpectralWeight.one.toCoeff q.val) n x : ℂ) := by
    exact hillHminusGapSquare_sqrt_eq_original_profile q n r V K hK hmatch hqV x hx
      (hpair.real_gap_mem_ball x hx)
      (hillHminus_real_gap_sqrt_continuousAt n r epsilon hr hepsilon K
        (hillOriginalHminusSource q.val) _ _ hpair hf hnorm x hx)
  unfold hillHminusGapBoundaryAction hillRealGapIntegral
  simp only [pow_zero,one_mul]
  rw [Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_ofNat ]
  congr 1
  rw [←intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr
  intro x hx
  exact he x (by simpa only [uIcc_of_le hle] using hx)

end NLS.KdV
