import NLS.KdV.HillHminusPhysicalGermDifferentials
import NLS.KdV.HillPhysicalActionGradients
import NLS.KdV.HillDiscriminantCotangentModes

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology MeasureTheory
namespace NLS.KdV

/-- Every genuine H-minus-one germ of the ORIGINAL action has the literal
original physical action differential on all even complex L2 directions. -/
theorem hillOriginalAction_hminus_fderiv_original
    (q : RealPeriodOneHillPotential) (n : ℕ+)
    (F : PeriodOneHminusOne → ℂ)
    (hF : AnalyticAt ℂ F (hillOriginalHminusSource q.val))
    (hmatch : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      F (hillOriginalHminusSource p.val) =
        (hillRealGapIntegral p.val p.property.1 p.property.2 n 0 : ℂ))
    (h : WeightedCoeff SpectralWeight.one.toWeight 2)
    (heven : SpectralWeight.one.toCoeff h ∈ Coeff.paritySubspace 0) :
    (fderiv ℂ F (hillOriginalHminusSource q.val)) (hillOriginalHminusSource h) =
      hillPhysicalDirectionPairing (SpectralWeight.one.toCoeff h)
        (hillPhysicalMomentGradient q.val q.property.1 q.property.2 n 0) := by
  let G := hillRealSourceMoment q.val q.property.1 q.property.2 n 0
  have hG := analyticAt_hillRealSourceMoment q.val q.property.1 q.property.2 n n.pos 0
  obtain ⟨V,hV,hqV,hGM⟩ := exists_hillRealSourceMoments_physical_neighborhood
    q.val q.property.1 q.property.2 n n.pos
  have hFG : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      F (hillOriginalHminusSource p.val) = G (SpectralWeight.one.toCoeff p.val) := by
    filter_upwards [hmatch,hV.mem_nhds hqV] with p hp hpV
    exact hp.trans (hGM p hpV 0).symm
  exact (hillHminusPhysicalGerm_fderiv_original q F G hF hG hFG h heven).trans
    (hillRealSourceMoment_gradient q.val q.property.1 q.property.2 n n.pos 0 _)

/-- All actual H-minus-one action gradients have the ORIGINAL unit Fourier
coefficients of the actual physical action contour. Low and closed gaps
are included; no gap-openness condition is used. -/
theorem hillOriginalAction_hminus_gradient_coefficients
    (q : RealPeriodOneHillPotential) (n : ℕ+)
    (F : PeriodOneHminusOne → ℂ)
    (hF : AnalyticAt ℂ F (hillOriginalHminusSource q.val))
    (hmatch : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      F (hillOriginalHminusSource p.val) =
        (hillRealGapIntegral p.val p.property.1 p.property.2 n 0 : ℂ)) (m : ℤ) :
    (NLS.Poisson.hminusScalarGradient F (hillOriginalHminusSource q.val)).val m =
      Fourier.unitFourierCoefficient (NLS.LinearVolterra.extend
        (hillPhysicalMomentGradient q.val q.property.1 q.property.2 n 0)) m := by
  let h := hillUnitWeightLift 2 (lp.single 2 (2*(-m)) 1)
  have hs : hillOriginalHminusSource h =
      WeightedCoeff.ofFinsupp (Weight.sobolev (-1)) 2 (Finsupp.single (-m) 1) := by
    apply Subtype.ext
    funext j
    simp [h,hillOriginalHminusSource_apply,WeightedCoeff.ofFinsupp_apply,lp.single_apply,
      Pi.single_apply,Finsupp.single_apply,show 2*j=-(2*m) ↔ j=-m by omega,eq_comm]
  have heven : SpectralWeight.one.toCoeff h ∈ Coeff.paritySubspace 0 := by
    rw [show SpectralWeight.one.toCoeff h=lp.single 2 (2*(-m)) 1 from toCoeff_hillUnitWeightLift _ _]
    apply Coeff.single_mem_paritySubspace
    omega
  rw [NLS.Poisson.hminusScalarGradient_apply,←hs,
    hillOriginalAction_hminus_fderiv_original q n F hF hmatch h heven]
  rw [show SpectralWeight.one.toCoeff h=lp.single 2 (2*(-m)) 1 from toCoeff_hillUnitWeightLift _ _,
    hillPhysicalDirectionPairing_apply]
  unfold Fourier.unitFourierCoefficient
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le (by norm_num : (0:ℝ)≤1)]
  filter_upwards [hillPhysicalDirection_single_lower_ae (2*(-m))] with x hx
  rw [hx,show 2*(-m)=-(2*m) by ring,mul_comm]

end NLS.KdV
