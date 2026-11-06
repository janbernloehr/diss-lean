import NLS.Articles.KdVConvexity.DirichletLocalInverse
import NLS.KdV.HillHminusOneDirichletJacobian

/-! # The actual bounded Hilbert spectral Jacobian at every real potential

The full derivative varies analytically on the same global complex
potential domain. Every coordinate is the original bounded H^-1 energy
or norming functional, with the exact energy weight 1+n. These identities
include arbitrary complex directions and all closed gaps.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
namespace NLS.Articles.KdVConvexity
open NLS.KdV

def DirichletHilbertCoordinates.fullMap (C : DirichletHilbertCoordinates)
    (q : PeriodOneHminusOne) : Coeff 2 × Coeff 2 := (C.energy q,C.norming q)

def DirichletHilbertCoordinates.jacobian (C : DirichletHilbertCoordinates)
    (q : PeriodOneHminusOne) : PeriodOneHminusOne →L[ℂ] (Coeff 2 × Coeff 2) := fderiv ℂ C.fullMap q

theorem DirichletHilbertCoordinates.analytic_fullMap (C : DirichletHilbertCoordinates) :
    AnalyticOnNhd ℂ C.fullMap C.domain := fun q hq => (C.analytic_energy q hq).prod (C.analytic_norming q hq)

theorem DirichletHilbertCoordinates.analytic_jacobian (C : DirichletHilbertCoordinates) :
    AnalyticOnNhd ℂ C.jacobian C.domain := C.analytic_fullMap.fderiv

theorem DirichletHilbertCoordinates.hasFDerivAt_fullMap (C : DirichletHilbertCoordinates)
    (q : PeriodOneHminusOne) (hq : q ∈ C.domain) : HasFDerivAt C.fullMap (C.jacobian q) q :=
  (C.analytic_fullMap q hq).differentiableAt.hasFDerivAt

theorem DirichletHilbertCoordinates.energy_coordinate_fderiv (C : DirichletHilbertCoordinates)
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (n : ℕ+) :
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 (actionIndexEquiv.symm n)).comp (fderiv ℂ C.energy q) =
      (1/(1+(n : ℕ) : ℂ)) • hillHminusDirichletEnergyDifferential q hr n := by
  ext h
  have hh := normalizedDirichletCoordinate_fderiv C.domain C.energy C.isOpen_domain C.analytic_energy
    C.root q (C.real_mem hr) hr n (C.energy_recovery q hr n) h
  change (fderiv ℂ C.energy q h) (actionIndexEquiv.symm n) =
    (1/(1+(n : ℕ) : ℂ))*hillHminusDirichletEnergyDifferential q hr n h
  rw [hillHminusDirichletEnergyDifferential_apply]
  rw [hh]
  simp only [div_eq_mul_inv,mul_inv,one_mul]
  ring

theorem DirichletHilbertCoordinates.norming_coordinate_fderiv (C : DirichletHilbertCoordinates)
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (n : ℕ+) :
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 (actionIndexEquiv.symm n)).comp (fderiv ℂ C.norming q) =
      hillHminusDirichletLogNormingDifferential q hr n := by
  let ev := lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 (actionIndexEquiv.symm n)
  have hK := (C.analytic_norming q (C.real_mem hr))
  have hscalar : AnalyticAt ℂ (fun p => C.norming p (actionIndexEquiv.symm n)) q :=
    (ev.analyticAt _).comp hK
  have hrec : ∀ᶠ p : PeriodOneRealHminusOne in 𝓝 (⟨q,hr⟩ : PeriodOneRealHminusOne),
      C.norming p.val (actionIndexEquiv.symm n) = (hillHminusDirichletLogNorming p.val p.property n : ℂ) :=
    Filter.Eventually.of_forall (fun p => C.norming_recovery p.val p.property n)
  have hd := hillHminusDirichletLogNorming_extension_hasFDerivAt
    (fun p => C.norming p (actionIndexEquiv.symm n)) ⟨q,hr⟩ hscalar n hrec
  exact (ev.hasFDerivAt.comp q hK.differentiableAt.hasFDerivAt).unique hd

theorem DirichletHilbertCoordinates.jacobian_energy (C : DirichletHilbertCoordinates)
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (n : ℕ+) (h : PeriodOneHminusOne) :
    (C.jacobian q h).1 (actionIndexEquiv.symm n) =
      hillHminusDirichletEnergyDifferential q hr n h/(1+(n : ℕ) : ℂ) := by
  have hcomp := (ContinuousLinearMap.fst ℂ (Coeff 2) (Coeff 2)).hasFDerivAt.comp q
    (C.hasFDerivAt_fullMap q (C.real_mem hr))
  have he : (C.jacobian q h).1 = fderiv ℂ C.energy q h := by
    have hh := congrArg (fun T : PeriodOneHminusOne →L[ℂ] Coeff 2 => T h) hcomp.fderiv
    simpa only [DirichletHilbertCoordinates.fullMap,Function.comp_def,ContinuousLinearMap.comp_apply] using! hh.symm
  rw [he]
  have hh := congrArg (fun T : PeriodOneHminusOne →L[ℂ] ℂ => T h) (C.energy_coordinate_fderiv q hr n)
  change (fderiv ℂ C.energy q h) (actionIndexEquiv.symm n) = (1/(1+(n : ℕ) : ℂ))*_ at hh
  simpa only [one_div,div_eq_mul_inv,mul_comm,one_mul] using! hh

theorem DirichletHilbertCoordinates.jacobian_norming (C : DirichletHilbertCoordinates)
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (n : ℕ+) (h : PeriodOneHminusOne) :
    (C.jacobian q h).2 (actionIndexEquiv.symm n) = hillHminusDirichletLogNormingDifferential q hr n h := by
  have hcomp := (ContinuousLinearMap.snd ℂ (Coeff 2) (Coeff 2)).hasFDerivAt.comp q
    (C.hasFDerivAt_fullMap q (C.real_mem hr))
  have he : (C.jacobian q h).2 = fderiv ℂ C.norming q h := by
    have hh := congrArg (fun T : PeriodOneHminusOne →L[ℂ] Coeff 2 => T h) hcomp.fderiv
    simpa only [DirichletHilbertCoordinates.fullMap,Function.comp_def,ContinuousLinearMap.comp_apply] using! hh.symm
  rw [he]
  exact congrArg (fun T : PeriodOneHminusOne →L[ℂ] ℂ => T h) (C.norming_coordinate_fderiv q hr n)

theorem DirichletHilbertCoordinates.hasFDerivAt_paired (C : DirichletHilbertCoordinates)
    (q : PeriodOneMeanZeroHminusOne) (hq : q.val ∈ C.domain) :
    HasFDerivAt C.paired ((C.jacobian q.val).comp periodOneMeanZeroInclusion) q :=
  (C.hasFDerivAt_fullMap q.val hq).comp q periodOneMeanZeroInclusion.hasFDerivAt

theorem DirichletHilbertCoordinates.jacobian_zero (C : DirichletHilbertCoordinates) :
    C.jacobian 0 = freeNormalizedDirichletLinearization.prod freeDirichletLogNormingLinearization := by
  have hr : IsRealPeriodOneHminusOne 0 := by intro k; simp
  exact (C.hasFDerivAt_fullMap 0 (C.real_mem hr)).unique (C.energy_derivative.prodMk C.norming_derivative)

theorem DirichletHilbertCoordinates.meanZero_jacobian_zero (C : DirichletHilbertCoordinates) :
    (C.jacobian 0).comp periodOneMeanZeroInclusion = freeDirichletFourierEquiv.toContinuousLinearMap := by
  rw [C.jacobian_zero]
  rfl

end NLS.Articles.KdVConvexity
