import NLS.Articles.KdVPseudomeasures.OriginalHillH1Hamiltonian
import NLS.KdV.HillMiuraFiniteGapProfile
import NLS.KdV.HillMiuraMeanNormalization
import NLS.MKdV.CenteredMiuraKdVHamiltonian
import NLS.Fourier.PeriodOneFourierUniqueness
import NLS.Fourier.UnitIntervalWeakDerivative

/-! Actual finite-gap Miura Fourier representatives recover the IDENTICAL
original physical H1 source and its exact KdV energy trace normalization. -/
noncomputable section
open Complex NLS.KdV NLS.MKdV NLS.WeightedCoeff NLS.ZakharovShabat NLS.Fourier
open scoped ContDiff
namespace NLS.Articles.KdVPseudomeasures

theorem hillH1_synthesis_eq_centered_finiteGap_Miura
    (q : RealSignedHilbert (signedStepOrder 0 1)) (u : PeriodOneRealL2) (c : ℝ)
    (hf : hillMiuraRealSource u ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (hi : periodOneMiura u.val=hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 q)+
      periodOneL2Inclusion (lp.single 2 0 (c:ℂ))) :
    (fun x : ℝ => periodOneSobolevSynthesis (signedOneRealToScalarDomain q) (x : AddCircle (2:ℝ)))=
      (fun x => miuraPotential (hillMiuraFiniteGapProfile u hf) x-(c:ℂ)) := by
  let Q := fun x : ℝ => periodOneSobolevSynthesis (signedOneRealToScalarDomain q) (x : AddCircle (2:ℝ))
  let f := hillMiuraFiniteGapProfile u hf
  have hs := contDiff_hillMiuraFiniteGapProfile u hf
  have hp := periodic_hillMiuraFiniteGapProfile u hf
  have hr : ContDiff ℝ ∞ (miuraPotential f) := (contDiff_infty_iff_deriv.mp hs).2.add (hs.pow 2)
  have hpr : Function.Periodic (miuraPotential f) 1 := by
    intro x
    exact congrArg₂ (fun a b : ℂ => a+b^2)
      (NLS.FunctionalAnalysis.periodic_deriv f 1 hp x) (hp x)
  have hcQ : Continuous Q := continuous_periodOneSobolevSynthesis _
  have he : miuraPotential f=(fun x => Q x+(c:ℂ)) := by
    apply eq_of_periodOneCoefficient_eq _ _ hr.continuous (hcQ.add continuous_const) hpr
      (by intro x; exact congrArg (fun z : ℂ => z+(c:ℂ)) (periodOneSobolevSynthesis_periodic _ x))
    intro n
    rw [periodOneCoefficient_miura_hillMiuraFiniteGapProfile]
    have hconst : periodOneCoefficient (fun _ : ℝ => (c:ℂ)) n=if n=0 then (c:ℂ) else 0 := by
      exact ((unitFourierCoefficient_eq_fourierCoeffOn _ n).symm).trans (unitFourierCoefficient_const _ _)
    have ha := periodOneCoefficient_add Q (fun _ => (c:ℂ)) hcQ continuous_const n
    change periodOneCoefficient (fun x => Q x+(c:ℂ)) n=
      periodOneCoefficient Q n+periodOneCoefficient (fun _ : ℝ => (c:ℂ)) n at ha
    rw [hconst] at ha
    have hQ : periodOneCoefficient Q n=q.val.val.val n := by
      rw [periodOneCoefficient_periodOneSobolevSynthesis,signedOneRealToScalarDomain_apply]
    rw [hQ] at ha
    have hn := congrArg (fun a : PeriodOneHminusOne => a.val n) hi
    simp only [WeightedCoeff.add_val,periodOneL2Inclusion_apply,
      lp.single_apply,Pi.single_apply] at hn
    have hraw : (hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 q)).val n=q.val.val.val n :=
      hillIntegerSourceInclusion_apply 1 q n
    rw [hraw] at hn
    exact hn.trans ha.symm
  funext x
  have hx := congrFun he x
  change Q x=miuraPotential f x-(c:ℂ)
  rw [hx]
  ring

/-- The literal physical H1 KdV Hamiltonian equals the SAME lift's actual
finite-gap NLS hierarchy combination, for EVERY real shift. -/
theorem hillH1KdVHamiltonian_finiteGap_Miura_trace
    (q : RealSignedHilbert (signedStepOrder 0 1)) (u : PeriodOneRealL2) (c : ℝ)
    (hf : hillMiuraRealSource u ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (hi : periodOneMiura u.val=hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 q)+
      periodOneL2Inclusion (lp.single 2 0 (c:ℂ))) :
    hillH1KdVHamiltonian q=((1/2:ℂ)*
      sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) (hillMiuraRealSource u) hf 5-
      3*(c:ℂ)*sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) (hillMiuraRealSource u) hf 3+
      2*(c:ℂ)^3).re := by
  have hc := hillMiura_shift_eq_norm_sq (hillIntegerSourceInclusion 1 q) u c hi
  have hm : (∫ x in (0:ℝ)..1, (hillMiuraFiniteGapProfile u hf x)^2)=(c:ℂ) := by
    rw [integral_sq_hillMiuraFiniteGapProfile,← hc]
  have he := classicalKdVHamiltonian_centered_miura_NLS (hillMiuraFiniteGapProfile u hf)
    (contDiff_hillMiuraFiniteGapProfile u hf) (periodic_hillMiuraFiniteGapProfile u hf) c hm
  rw [← sourceFiniteGapNLSHamiltonian_hillMiura_eq_classical,
    ← sourceFiniteGapNLSHamiltonian_hillMiura_eq_classical] at he
  unfold hillH1KdVHamiltonian
  rw [periodOneKdVHamiltonian_eq_classical,hillH1_synthesis_eq_centered_finiteGap_Miura q u c hf hi,he]

end NLS.Articles.KdVPseudomeasures
