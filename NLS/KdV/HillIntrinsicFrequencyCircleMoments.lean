import NLS.KdV.HillIntrinsicCircleEndpoints
import NLS.KdV.HillIntrinsicFrequencyMoments
import NLS.KdV.HillHminusOneMiuraFrequencySeries
import NLS.ComplexAnalysis.CircleSquaredBandHomotopy
import NLS.ComplexAnalysis.NonrealCircleIntegralVectorComparison

/-! Exact moment transfer from the original frequency circles to intrinsic
physical gap circles. The homotopy stays on the physical cut and retains the
shifted logarithm, canonical root and quadratic Jacobian at every order. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
namespace NLS.KdV

/-- Matched spectral bands suffice for the full shifted-primitive moment
comparison; neither a finite-gap nor an open-own-gap premise is needed. -/
theorem hillPhysical_frequency_circle_moment_eq_intrinsic
    (q : RealPeriodOneHillPotential) (n k : ℕ+) (m : ℕ)
    (hcross : (Real.pi*(k : ℝ)-Real.pi/4)^2 ∈
      Ioo (hillRealLabels q.val q.property.1 q.property.2 (2*(k : ℕ)-2))
        (hillRealLabels q.val q.property.1 q.property.2 (2*(k : ℕ)-1)) ∧
      (Real.pi*(k : ℝ)+Real.pi/4)^2 ∈
      Ioo (hillRealLabels q.val q.property.1 q.property.2 (2*(k : ℕ)))
        (hillRealLabels q.val q.property.1 q.property.2 (2*(k : ℕ)+1))) :
    (∮ z in C((Real.pi : ℂ)*(k : ℕ),Real.pi/4),
      (hillL2ShiftedPrimitive q.val k (z^2))^m*
        (hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n n.pos (z^2)/
          hillEnergyCanonicalRootProduct q.val q.property.1 q.property.2 (z^2))*(2*z)) =
      hillIntrinsicFrequencyMoment q.val q.property.1 q.property.2 n n.pos k m := by
  let d := hillRealGapCenter q.val q.property.1 q.property.2 k
  let R := hillRealGapHalfLength q.val q.property.1 q.property.2 k+
    hillRealGapCollar q.val q.property.1 q.property.2 k
  let c := Real.pi*(k : ℝ)
  let r := Real.pi/4
  let f := fun E => (hillL2ShiftedPrimitive q.val k E)^m*
    (hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n n.pos E/
      hillEnergyCanonicalRootProduct q.val q.property.1 q.property.2 E)
  have hR : 0<R := add_pos_of_nonneg_of_pos
    (hillRealGapContour_geometry q.val q.property.1 q.property.2 k k.pos).1
    (hillRealGapContour_geometry q.val q.property.1 q.property.2 k k.pos).2.1
  have hr : 0<r := by dsimp only [r];positivity
  have hrc : r<c := by
    have hk : (1 : ℝ)≤k := by exact_mod_cast k.pos
    dsimp only [r,c]
    nlinarith [Real.pi_pos]
  have hk1 := k.pos
  have hD (E : ℂ) (hE : E.im≠0 ∨
      E.re∈Ioo (hillRealLabels q.val q.property.1 q.property.2 (2*(k : ℕ)-2))
        (hillRealLabels q.val q.property.1 q.property.2 (2*(k : ℕ)-1)) ∨
      E.re∈Ioo (hillRealLabels q.val q.property.1 q.property.2 (2*(k : ℕ)))
        (hillRealLabels q.val q.property.1 q.property.2 (2*(k : ℕ)+1))) :
      E∈hillL2RealCutDomain q.val q.property.1 q.property.2 := by
    rcases hE with hE | hE | hE
    · exact Or.inl hE
    · exact Or.inr ⟨(k : ℕ)-1,by simpa only [show 2*((k : ℕ)-1)=2*(k : ℕ)-2 by omega,
        show 2*(k : ℕ)-2+1=2*(k : ℕ)-1 by omega] using hE⟩
    · exact Or.inr ⟨(k : ℕ),hE⟩
  have hf : AnalyticOnNhd ℂ f (hillL2RealCutDomain q.val q.property.1 q.property.2) := by
    intro E hE
    have hF : AnalyticAt ℂ (hillL2ShiftedPrimitive q.val k) E :=
      (analyticOnNhd_hillL2RealCutPrimitive q.val q.property.1 q.property.2 E hE).add analyticAt_const
    exact (hF.pow m).mul ((analyticOnNhd_hillAbelianSelectedGlobalPsi_energy
      q.val q.property.1 q.property.2 n n.pos E (mem_univ _)).div
      (analyticOnNhd_hillEnergyCanonicalRootProduct q.val q.property.1 q.property.2 E hE)
      (hillEnergyCanonicalRootProduct_ne_zero_on_realCutDomain q.val q.property.1 q.property.2 E hE))
  obtain ⟨hld,hud⟩ := hillIntrinsicCircle_endpoints_in_bands q k
  have hh := circleIntegral_squared_pullback_eq_circle_of_real_bands f
    (hillL2RealCutDomain q.val q.property.1 q.property.2) d R c r
    (hillRealLabels q.val q.property.1 q.property.2 (2*(k : ℕ)-2))
    (hillRealLabels q.val q.property.1 q.property.2 (2*(k : ℕ)-1))
    (hillRealLabels q.val q.property.1 q.property.2 (2*(k : ℕ)))
    (hillRealLabels q.val q.property.1 q.property.2 (2*(k : ℕ)+1))
    hR hr hrc hld hcross.1 hud hcross.2 hD hf
  simpa only [f,d,R,c,r,ofReal_mul,ofReal_natCast,hillIntrinsicFrequencyMoment,frequencyMoment] using hh

/-- Original source sheets identify the complete rough-circle moment with
its physical frequency-circle integral. Nonreal equality suffices at the two
real crossings, so no continuation across a physical gap is asserted. -/
theorem hillHminusMiuraMoment_eq_physical_frequency_circle
    (C : HillHminusMiuraChart)
    (s : (n : ℤ) → NLS.CoeffPair 2 → NLS.DeletedCoeff 2 n)
    (q : RealPeriodOneHillPotential) (n k : ℕ+) (m : ℕ)
    (hnum : ∀ E : ℂ, hillHminusMiuraEnergyPsi C s (n : ℤ) (E,hillOriginalHminusSource q.val) =
      hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n n.pos E) :
    hillHminusMiuraMoment C s n k m (hillOriginalHminusSource q.val) =
    ∮ z in C((Real.pi : ℂ)*(k : ℕ),Real.pi/4),
      (hillL2ShiftedPrimitive q.val k (z^2))^m*
        (hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n n.pos (z^2)/
          hillEnergyCanonicalRootProduct q.val q.property.1 q.property.2 (z^2))*(2*z) := by
  unfold hillHminusMiuraMoment
  have hc : (Real.pi : ℂ)*(k : ℕ) = (Real.pi*(k : ℝ) : ℝ) := by simp only [ofReal_mul,ofReal_natCast]
  rw [hc]
  apply circleIntegral_eq_of_eq_on_nonreal_vector _ _ _ _ (by positivity)
  intro z hz hzi
  have hre := re_bounds_of_mem_realCenteredClosedBall (sphere_subset_closedBall hz)
  have hk : (1 : ℝ)≤k := by exact_mod_cast k.pos
  have hzr : 0<z.re := by nlinarith [hre.1,Real.pi_pos]
  have hE : (z^2).im≠0 := by
    rw [pow_two,mul_im]
    rw [show z.re*z.im+z.im*z.re=2*z.re*z.im by ring]
    exact mul_ne_zero (mul_ne_zero (by norm_num : (2 : ℝ)≠0) hzr.ne') hzi
  have ht := mem_hillL2ContinuationDomain_of_im_ne_zero q.val q.property.1 q.property.2 (z^2) hE
  dsimp only [hillHminusFrequencyPrimitive,hillL2ShiftedPrimitive]
  rw [hillHminusContinuedPrimitive_original_source_agreement q.val q.property.1 _ ht,
    hillHminusContinuedRoot_original_source_agreement q.val q.property.1 _ ht,hnum,
    hillL2RealCutPrimitive,if_neg hE,
    hillEnergyCanonicalRootProduct_eq_continued_of_mem q.val q.property.1 q.property.2 _ (Or.inl hE) ht]

end NLS.KdV
