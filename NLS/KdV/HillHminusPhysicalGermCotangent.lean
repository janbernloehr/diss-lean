import NLS.KdV.HillHminusPhysicalGermDifferentials
import NLS.KdV.HillNativeCotangentExtension

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
namespace NLS.KdV

/-- A physically matched H-minus-one germ has exactly the H1 cotangent
already proved for its original native Hilbert differential. -/
theorem hillHminusPhysicalGerm_gradient_eq_of_native_restriction
    (q : RealPeriodOneHillPotential) (F : PeriodOneHminusOne → ℂ) (G : Coeff 2 → ℂ)
    (hF : AnalyticAt ℂ F (hillOriginalHminusSource q.val))
    (hG : AnalyticAt ℂ G (SpectralWeight.one.toCoeff q.val))
    (hmatch : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      F (hillOriginalHminusSource p.val) = G (SpectralWeight.one.toCoeff p.val))
    (a : WeightedCoeff (Weight.sobolev 1) 2)
    (ha : (fderiv ℂ G (SpectralWeight.one.toCoeff q.val)).comp hillNativeHilbertDirection =
      (WeightedCoeff.sobolevBilinearPairing 1 a).comp NLS.Poisson.hilbertToHminus) :
    NLS.Poisson.hminusScalarGradient F (hillOriginalHminusSource q.val) = a := by
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
  rw [NLS.Poisson.hminusScalarGradient_apply,←hs,
    hillHminusPhysicalGerm_fderiv_original q F G hF hG hmatch h heven]
  have he := congrArg (fun L : Coeff 2 →L[ℂ] ℂ => L (lp.single 2 (-m) 1)) ha
  change (fderiv ℂ G (SpectralWeight.one.toCoeff q.val))
      (Coeff.insert (Coeff.parityEmbedding 0) (lp.single 2 (-m) 1)) =
    WeightedCoeff.sobolevBilinearPairing 1 a (NLS.Poisson.hilbertToHminus (lp.single 2 (-m) 1)) at he
  rw [Coeff.insert_single,Coeff.parityEmbedding_apply,add_zero] at he
  simpa [h,WeightedCoeff.sobolevBilinearPairing_apply,NLS.Poisson.hilbertToHminus_apply,
    lp.single_apply,Pi.single_apply] using he

end NLS.KdV
