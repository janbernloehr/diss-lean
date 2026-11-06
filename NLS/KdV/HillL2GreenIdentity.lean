import NLS.KdV.HillL2StateCurve
import NLS.KdV.HillL2Conjugation

/-! # The scalar Green identity for real rough L2 Hill potentials. -/

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology MeasureTheory Matrix
open scoped ComplexConjugate ENNReal
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis
namespace NLS.KdV

theorem scalarStateMass_eq_classical (Q : C(AddCircle (2 : ℝ),ℂ)) (z : ℂ) (v : ℂ × ℂ) :
    scalarStateMass (hillL2FrequencyStateCurve (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) z v) =
      ∫ x in (0 : ℝ)..1, normSq (classicalHillFlow (hillUnitPotentialCurve Q) (z^2) v x).1 := by
  rw [scalarStateMass_eq_integral]
  apply intervalIntegral.integral_congr
  intro x hx
  have hx' : x∈Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le (by norm_num : (0 : ℝ)≤1)] using hx
  simp only [NLS.LinearVolterra.extend,projIcc_of_mem _ hx',hillL2FrequencyStateCurve_eq_classical]

theorem hillL2FrequencyStateCurve_green_im (q : Coeff 2) (hq : IsRealHillPotential q) (z : ℂ) (v : ℂ × ℂ) :
    -(z^2).im*scalarStateMass (hillL2FrequencyStateCurve q z v) =
      (conj (hillL2FrequencyStateCurve q z v ⟨1,by norm_num⟩).1*
        (hillL2FrequencyStateCurve q z v ⟨1,by norm_num⟩).2).im-(conj v.1*v.2).im := by
  let S : Coeff 2 → Coeff 2 := fun a => (1/2 : ℂ) • (a+star (Coeff.reflection a))
  have hS : Continuous S := (continuous_id.add (Coeff.reflection.continuous.star)).const_smul (1/2 : ℂ)
  let G : Coeff 2 → ℝ := fun a => -(z^2).im*scalarStateMass (hillL2FrequencyStateCurve a z v)-
      ((conj (hillL2FrequencyStateCurve a z v ⟨1,by norm_num⟩).1*
        (hillL2FrequencyStateCurve a z v ⟨1,by norm_num⟩).2).im-(conj v.1*v.2).im)
  have hc : Continuous G := by
    have hm := continuous_scalarStateMass.comp (continuous_hillL2FrequencyStateCurve z v)
    have he : Continuous (fun a : Coeff 2 => hillL2FrequencyStateCurve a z v ⟨1,by norm_num⟩) :=
      (continuous_eval_const _).comp (continuous_hillL2FrequencyStateCurve z v)
    exact (continuous_const.mul hm).sub ((continuous_im.comp (he.fst.star.mul he.snd)).sub continuous_const)
  have hfinite (a : ℤ →₀ ℂ) : G (S (Coeff.ofFinsupp a))=0 := by
    let Q := Fourier.continuousSynthesis (Coeff.ofFinsupp (p := 1) a)
    let R : C(AddCircle (2 : ℝ),ℂ) := (1/2 : ℂ) • (Q+star Q)
    have hQ : Fourier.continuousFourierCLM Q=Coeff.ofFinsupp (p := 2) a := by
      ext k
      rw [Fourier.continuousFourierCLM_apply]
      exact Fourier.fourierCoeff_continuousSynthesis _ k
    have hcoeff (T : C(AddCircle (2 : ℝ),ℂ)) :
        SpectralWeight.one.toCoeff (hillContinuousCoefficients T)=Fourier.continuousFourierCLM T := by
      ext k
      simp only [SpectralWeight.toCoeff_apply,hillContinuousCoefficients_apply,Fourier.continuousFourierCLM_apply]
    have hR : SpectralWeight.one.toCoeff (hillContinuousCoefficients R)=S (Coeff.ofFinsupp a) := by
      rw [hcoeff]
      dsimp only [R,S]
      rw [map_smul,map_add,Fourier.continuousFourierCLM_star,hQ]
    have hr : ∀ t, (hillUnitPotentialCurve R t).im=0 := by
      intro t
      simp [R,hillUnitPotentialCurve,Complex.mul_im]
    dsimp only [G]
    rw [← hR,scalarStateMass_eq_classical,hillL2FrequencyStateCurve_eq_classical]
    exact sub_eq_zero.mpr (classicalHillGreen_im_identity (hillUnitPotentialCurve R) (z^2) v hr)
  have he : (fun a : Coeff 2 => G (S a))=(fun _ : Coeff 2 => (0 : ℝ)) :=
    (Coeff.denseRange_ofFinsupp (p := 2) (by simp)).equalizer (hc.comp hS) continuous_const (funext hfinite)
  have hfix : S q=q := by
    ext k
    simp only [S,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,lp.coeFn_add,Pi.add_apply,
      lp.star_apply,Coeff.reflection_apply,hq k,starRingEnd_apply,star_star]
    ring
  have hh := congrFun he q
  rw [hfix] at hh
  exact sub_eq_zero.mp hh

end NLS.KdV
