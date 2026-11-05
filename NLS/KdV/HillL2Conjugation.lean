import NLS.KdV.ClassicalHillConjugation
import NLS.KdV.HillRealSpectrum
import NLS.KdV.HillCharacteristicZeros
import NLS.Fourier.ContinuousConjugation

/-! # Schwarz symmetry of the actual rough Hill energy trace

The scalar-flow conjugation theorem is extended in the L2 norm by
Fourier density. Symmetrizing the physical functions preserves reality
before taking the limit. No real-type assertion about the first-order
pair `(-1,-q)` is used.
-/

noncomputable section
open Set MeasureTheory Complex
open scoped ComplexConjugate
namespace NLS.KdV

theorem hillL2Discriminant_conj (q : Coeff 2) (hreal : IsRealHillPotential q) (z : ℂ) :
    hillL2Discriminant q (conj z) = conj (hillL2Discriminant q z) := by
  let S : Coeff 2 → Coeff 2 := fun a => (1/2 : ℂ) • (a+star (Coeff.reflection a))
  have hS : Continuous S :=
    (continuous_id.add (Coeff.reflection.continuous.star)).const_smul (1/2 : ℂ)
  have hc (w : ℂ) : Continuous (fun a : Coeff 2 => hillL2Discriminant (S a) w) := by
    have hD : Continuous (fun p : ℂ × Coeff 2 => hillL2Discriminant p.2 p.1) :=
      continuous_iff_continuousAt.mpr
        (fun p => (analyticOnNhd_hillL2Discriminant_joint p (mem_univ _)).continuousAt)
    have hm : Continuous (fun a : Coeff 2 => (w,S a)) := continuous_const.prodMk hS
    convert! hD.comp hm using 1
  have hcoeff (Q : C(AddCircle (2 : ℝ), ℂ)) :
      SpectralWeight.one.toCoeff (hillContinuousCoefficients Q) = Fourier.continuousFourierCLM Q := by
    ext k
    simp only [SpectralWeight.toCoeff_apply,hillContinuousCoefficients_apply,
      Fourier.continuousFourierCLM_apply]
  have hfinite (a : ℤ →₀ ℂ) :
      hillL2Discriminant (S (Coeff.ofFinsupp a)) (conj z) =
        conj (hillL2Discriminant (S (Coeff.ofFinsupp a)) z) := by
    let Q := Fourier.continuousSynthesis (Coeff.ofFinsupp (p := 1) a)
    let R : C(AddCircle (2 : ℝ), ℂ) := (1/2 : ℂ) • (Q+star Q)
    have hQ : Fourier.continuousFourierCLM Q = Coeff.ofFinsupp (p := 2) a := by
      ext k
      rw [Fourier.continuousFourierCLM_apply]
      exact Fourier.fourierCoeff_continuousSynthesis _ k
    have hR : SpectralWeight.one.toCoeff (hillContinuousCoefficients R) = S (Coeff.ofFinsupp a) := by
      rw [hcoeff]
      dsimp only [R,S]
      rw [map_smul,map_add,Fourier.continuousFourierCLM_star,hQ]
    have hr : ∀ t, (hillUnitPotentialCurve R t).im = 0 := by
      intro t
      simp [R,hillUnitPotentialCurve,Complex.mul_im]
    rw [← hR,hillL2Discriminant_eq_classical,hillL2Discriminant_eq_classical]
    exact classicalHillDiscriminant_conj _ hr z
  have he : (fun a : Coeff 2 => hillL2Discriminant (S a) (conj z)) =
      (fun a : Coeff 2 => conj (hillL2Discriminant (S a) z)) :=
    (Coeff.denseRange_ofFinsupp (p := 2) (by simp)).equalizer (hc _) (hc z).star (funext hfinite)
  have hfix : S q = q := by
    ext k
    simp only [S,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,lp.coeFn_add,Pi.add_apply,
      lp.star_apply,Coeff.reflection_apply,hreal k,starRingEnd_apply,star_star]
    ring
  simpa only [hfix] using congrFun he q

theorem hillL2Discriminant_real (q : Coeff 2) (hreal : IsRealHillPotential q) (x : ℝ) :
    (hillL2Discriminant q x).im = 0 := by
  have he := congrArg Complex.im (hillL2Discriminant_conj q hreal (x : ℂ))
  simp only [conj_ofReal,conj_im] at he
  linarith

theorem hillL2Radicand_conj (q : Coeff 2) (hreal : IsRealHillPotential q) (z : ℂ) :
    hillL2Radicand q (conj z) = conj (hillL2Radicand q z) := by
  simp only [hillL2Radicand,hillL2Discriminant_conj q hreal,map_sub,map_pow,map_ofNat]

end NLS.KdV
