import NLS.KdV.HillHminusDirichletCharts
import NLS.KdV.HillPhysicalGermDerivativeUniqueness
import NLS.KdV.HillDirichletGardnerBrackets
import NLS.KdV.HillUnitWeightLift
import NLS.KdV.HillNativeCotangentExtension

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology MeasureTheory
namespace NLS.KdV

/-- Physical matching fixes the actual H-minus-one Dirichlet energy
differential on every original complex even source direction. -/
theorem hillDirichletEnergy_hminus_fderiv_original
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n)
    (k : PeriodOneHminusOne → ℂ) (hk : AnalyticAt ℂ k (hillOriginalHminusSource q.val))
    (hmatch : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      k (hillOriginalHminusSource p.val)=
        (hillDirichletEnergy p.val p.property.1 p.property.2 n hn : ℂ))
    (h : WeightedCoeff SpectralWeight.one.toWeight 2)
    (heven : SpectralWeight.one.toCoeff h∈Coeff.paritySubspace 0) :
    (fderiv ℂ k (hillOriginalHminusSource q.val)) (hillOriginalHminusSource h)=
      hillPhysicalDirectionPairing (SpectralWeight.one.toCoeff h) (hillDirichletGradientCurve q n hn) := by
  obtain ⟨a,ha,ha0,hroot,hamatch⟩ := exists_hillDirichletEnergy_analytic_extension q n hn
  let G : Coeff 2 → ℂ := a
  have hG : AnalyticAt ℂ G (SpectralWeight.one.toCoeff q.val) := ha
  have hGmatch : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      G (SpectralWeight.one.toCoeff p.val)=
        (hillDirichletEnergy p.val p.property.1 p.property.2 n hn : ℂ) := hamatch
  have heq := hillPhysicalGerm_fderiv_eq_of_eventuallyEq q.val q.property.1 q.property.2
    (fun p => k (hillOriginalHminusSource p)) (fun p => G (SpectralWeight.one.toCoeff p))
    (hk.comp (hillOriginalHminusSource.analyticAt q.val))
    (hG.comp (SpectralWeight.one.toCoeff.analyticAt q.val))
    (by filter_upwards [hmatch,hGmatch] with p hp hg; exact hp.trans hg.symm) h heven
  have hl := hk.differentiableAt.hasFDerivAt.comp q.val hillOriginalHminusSource.hasFDerivAt
  have hr := hG.differentiableAt.hasFDerivAt.comp q.val SpectralWeight.one.toCoeff.hasFDerivAt
  change (fderiv ℂ (k ∘ hillOriginalHminusSource) q.val) h=
    (fderiv ℂ (G ∘ SpectralWeight.one.toCoeff) q.val) h at heq
  rw [hl.fderiv,hr.fderiv] at heq
  simp only [ContinuousLinearMap.comp_apply] at heq
  apply heq.trans
  rw [hillPhysicalDirectionPairing_apply]
  exact hillDirichletGradient_represents_branch q n hn a ha ha0 hroot
    (SpectralWeight.one.toCoeff h)

/-- Every coefficient of an actual analytic H-minus-one Dirichlet-energy germ
is the literal unit Fourier coefficient of the original physical gradient. -/
theorem hillDirichletEnergy_hminus_gradient_coefficients
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n)
    (k : PeriodOneHminusOne → ℂ) (hk : AnalyticAt ℂ k (hillOriginalHminusSource q.val))
    (hmatch : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      k (hillOriginalHminusSource p.val)=
        (hillDirichletEnergy p.val p.property.1 p.property.2 n hn : ℂ)) (m : ℤ) :
    (NLS.Poisson.hminusScalarGradient k (hillOriginalHminusSource q.val)).val m=
      Fourier.unitFourierCoefficient (NLS.LinearVolterra.extend (hillDirichletGradientCurve q n hn)) m := by
  let h := hillUnitWeightLift 2 (lp.single 2 (2*(-m)) 1)
  have hs : hillOriginalHminusSource h=
      WeightedCoeff.ofFinsupp (Weight.sobolev (-1)) 2 (Finsupp.single (-m) 1) := by
    apply Subtype.ext
    funext j
    simp [h,hillOriginalHminusSource_apply,WeightedCoeff.ofFinsupp_apply,lp.single_apply,
      Pi.single_apply,Finsupp.single_apply,show 2*j=-(2*m)↔j=-m by omega,eq_comm]
  have heven : SpectralWeight.one.toCoeff h∈Coeff.paritySubspace 0 := by
    rw [show SpectralWeight.one.toCoeff h=lp.single 2 (2*(-m)) 1 from toCoeff_hillUnitWeightLift _ _]
    apply Coeff.single_mem_paritySubspace
    omega
  rw [NLS.Poisson.hminusScalarGradient_apply,←hs,
    hillDirichletEnergy_hminus_fderiv_original q n hn k hk hmatch h heven]
  rw [show SpectralWeight.one.toCoeff h=lp.single 2 (2*(-m)) 1 from toCoeff_hillUnitWeightLift _ _,
    hillPhysicalDirectionPairing_apply]
  unfold Fourier.unitFourierCoefficient
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le (by norm_num : (0 : ℝ)≤1)]
  filter_upwards [hillPhysicalDirection_single_lower_ae (2*(-m))] with x hx
  rw [hx,show 2*(-m)=-(2*m) by ring,mul_comm]

end NLS.KdV
