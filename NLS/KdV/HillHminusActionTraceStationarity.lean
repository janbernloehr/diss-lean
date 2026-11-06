import NLS.KdV.HillMeanZeroActionTraceKernel
import NLS.KdV.HillGardnerOriginalHilbertDirection
import NLS.KdV.HillHminusActionDefectCurve
import NLS.KdV.HillHminusTraceHamiltonianVector

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open NLS.Poisson
namespace NLS.KdV

/-- Stationarity along ALL actual physical action sources implies
stationarity along EVERY actual fixed-energy physical trace source.
The Hamiltonian direction used for interpolation is the literal
mean-zero ORIGINAL complex L2 representative of the true Gardner vector. -/
theorem hillHminus_trace_stationary_of_all_action_sources
    (q : RealPeriodOneHillPotential) (D : PeriodOneHminusOne → ℂ)
    (hkernel : ∀ n : ℕ+, (fderiv ℂ D (hillOriginalHminusSource q.val))
      (hillOriginalHminusSource (hillPhysicalMomentHamiltonianSource
        q.val q.property.1 q.property.2 n n.pos 0)) = 0) (E : ℂ) :
    hminusGardnerBracket D (fun a => hillHminusDiscriminant a E) (hillOriginalHminusSource q.val) = 0 ∧
      (fderiv ℂ D (hillOriginalHminusSource q.val))
        (hillOriginalHminusSource (hillEnergyHamiltonianSource (SpectralWeight.one.toCoeff q.val) E)) = 0 := by
  let L := fderiv ℂ D (hillOriginalHminusSource q.val)
  let V := hillGardnerOriginalHilbertDirection L
  have heven : SpectralWeight.one.toCoeff V ∈ Coeff.paritySubspace 0 :=
    hillGardnerOriginalHilbertDirection_even L
  have hzero : (SpectralWeight.one.toCoeff V) 0 = 0 := by
    rw [SpectralWeight.toCoeff_apply]
    exact hillGardnerOriginalHilbertDirection_mean_zero L
  have hV : hillOriginalHminusSource V = gardnerHamiltonianVector D (hillOriginalHminusSource q.val) :=
    hillGardnerOriginalHilbertDirection_source L
  have hactions (n : ℕ+) : (fderiv ℂ (hillRealSourceMoment q.val q.property.1 q.property.2 n 0)
      (SpectralWeight.one.toCoeff q.val)) (SpectralWeight.one.toCoeff V) = 0 := by
    obtain ⟨J,hJ,hJM⟩ := exists_hillOriginal_action_hminus_physical_germ q n
    have hDJ : hminusGardnerBracket D J (hillOriginalHminusSource q.val) = 0 := by
      rw [←fderiv_apply_gardnerHamiltonianVector,
        hillOriginalAction_hminus_HamiltonianVector_eq_neg_source q n J hJ hJM,map_neg,hkernel n,neg_zero]
    have hJD : (fderiv ℂ J (hillOriginalHminusSource q.val)) (hillOriginalHminusSource V) = 0 := by
      rw [hV,fderiv_apply_gardnerHamiltonianVector,hminusGardnerBracket_antisymm,hDJ,neg_zero]
    rw [hillOriginalAction_hminus_fderiv_original q n J hJ hJM V heven] at hJD
    rw [hillRealSourceMoment_gradient q.val q.property.1 q.property.2 n n.pos 0]
    exact hJD
  have htrace := hillOriginalTrace_variation_zero_of_mean_zero_action_kernel
    q (SpectralWeight.one.toCoeff V) heven hzero hactions E
  let T : PeriodOneHminusOne → ℂ := fun a => hillHminusDiscriminant a E
  have hT : AnalyticAt ℂ T (hillOriginalHminusSource q.val) :=
    analyticAt_hillHminusDiscriminant_source _ E
  have hG : AnalyticAt ℂ (fun a : Coeff 2 => hillL2Discriminant a E) (SpectralWeight.one.toCoeff q.val) :=
    (analyticOnNhd_hillL2Discriminant_joint (E,SpectralWeight.one.toCoeff q.val) (mem_univ _)).comp
      (f := fun a : Coeff 2 => (E,a)) (analyticAt_const.prod analyticAt_id)
  have hTM : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      T (hillOriginalHminusSource p.val) = hillL2Discriminant (SpectralWeight.one.toCoeff p.val) E :=
    Eventually.of_forall (fun p => hillHminusDiscriminant_original_source_agreement p.val p.property.1 E)
  have hTD : hminusGardnerBracket T D (hillOriginalHminusSource q.val) = 0 := by
    rw [←fderiv_apply_gardnerHamiltonianVector,←hV,
      hillHminusPhysicalGerm_fderiv_original q T _ hT hG hTM V heven]
    exact htrace
  have hDT : hminusGardnerBracket D T (hillOriginalHminusSource q.val) = 0 := by
    rw [hminusGardnerBracket_antisymm,hTD,neg_zero]
  refine ⟨hDT,?_⟩
  rw [←fderiv_apply_gardnerHamiltonianVector,
    hillHminusDiscriminant_HamiltonianVector_eq_neg_source q E,map_neg] at hDT
  exact neg_eq_zero.mp hDT

end NLS.KdV
