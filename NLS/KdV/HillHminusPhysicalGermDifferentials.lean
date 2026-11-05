import NLS.KdV.HillPhysicalGermDerivativeUniqueness
import NLS.KdV.HillHminusOriginalSheets
import NLS.KdV.HillUnitWeightLift
import NLS.Poisson.HminusGardnerBracket

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
namespace NLS.KdV

/-- Original real L2 germ matching fixes every original complex even
physical direction of an analytic H-minus-one differential. -/
theorem hillHminusPhysicalGerm_fderiv_original
    (q : RealPeriodOneHillPotential)
    (F : PeriodOneHminusOne → ℂ) (G : Coeff 2 → ℂ)
    (hF : AnalyticAt ℂ F (hillOriginalHminusSource q.val))
    (hG : AnalyticAt ℂ G (SpectralWeight.one.toCoeff q.val))
    (hmatch : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      F (hillOriginalHminusSource p.val) = G (SpectralWeight.one.toCoeff p.val))
    (h : WeightedCoeff SpectralWeight.one.toWeight 2)
    (heven : SpectralWeight.one.toCoeff h ∈ Coeff.paritySubspace 0) :
    (fderiv ℂ F (hillOriginalHminusSource q.val)) (hillOriginalHminusSource h) =
      (fderiv ℂ G (SpectralWeight.one.toCoeff q.val)) (SpectralWeight.one.toCoeff h) := by
  have heq := hillPhysicalGerm_fderiv_eq_of_eventuallyEq q.val q.property.1 q.property.2
    (F ∘ hillOriginalHminusSource) (G ∘ SpectralWeight.one.toCoeff)
    (hF.comp (hillOriginalHminusSource.analyticAt q.val))
    (hG.comp (SpectralWeight.one.toCoeff.analyticAt q.val)) hmatch h heven
  have hl := hF.differentiableAt.hasFDerivAt.comp q.val hillOriginalHminusSource.hasFDerivAt
  have hr := hG.differentiableAt.hasFDerivAt.comp q.val SpectralWeight.one.toCoeff.hasFDerivAt
  rw [hl.fderiv,hr.fderiv] at heq
  exact heq

/-- Agreement only as ORIGINAL real L2 germs determines the ENTIRE complex
H-minus-one differential. The unit modes are actual original even modes. -/
theorem hillHminusPhysicalGerm_fderiv_eq_of_eventuallyEq
    (q : RealPeriodOneHillPotential) (F G : PeriodOneHminusOne → ℂ)
    (hF : AnalyticAt ℂ F (hillOriginalHminusSource q.val))
    (hG : AnalyticAt ℂ G (hillOriginalHminusSource q.val))
    (hmatch : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      F (hillOriginalHminusSource p.val) = G (hillOriginalHminusSource p.val)) :
    fderiv ℂ F (hillOriginalHminusSource q.val) =
      fderiv ℂ G (hillOriginalHminusSource q.val) := by
  have hgrad : NLS.Poisson.hminusScalarGradient F (hillOriginalHminusSource q.val) =
      NLS.Poisson.hminusScalarGradient G (hillOriginalHminusSource q.val) := by
    apply Subtype.ext
    funext m
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
    have heq := hillPhysicalGerm_fderiv_eq_of_eventuallyEq q.val q.property.1 q.property.2
      (F ∘ hillOriginalHminusSource) (G ∘ hillOriginalHminusSource)
      (hF.comp (hillOriginalHminusSource.analyticAt q.val))
      (hG.comp (hillOriginalHminusSource.analyticAt q.val)) hmatch h heven
    have hl := hF.differentiableAt.hasFDerivAt.comp q.val hillOriginalHminusSource.hasFDerivAt
    have hr := hG.differentiableAt.hasFDerivAt.comp q.val hillOriginalHminusSource.hasFDerivAt
    rw [hl.fderiv,hr.fderiv] at heq
    simpa only [NLS.Poisson.hminusScalarGradient_apply,ContinuousLinearMap.comp_apply,hs] using heq
  ext v
  rw [NLS.Poisson.hminusScalarGradient_represents,
    NLS.Poisson.hminusScalarGradient_represents,hgrad]

end NLS.KdV
