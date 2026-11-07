import NLS.KdV.HillMiuraInverseMoment
import NLS.ZakharovShabat.SourceFiniteGapNLSHamiltonians
import NLS.Fourier.SmoothPeriodOneCoefficientAlgebra
import NLS.MKdV.MiuraClassicalSolution

/-! Actual smooth Fourier representatives of a genuine finite-gap scalar
Miura lift, with the ENTIRE coefficients, original mass and hierarchy. -/
noncomputable section
open Complex NLS.Fourier NLS.ZakharovShabat
open scoped ContDiff
namespace NLS.KdV

def hillMiuraFiniteGapProfile (u : PeriodOneRealL2)
    (hf : hillMiuraRealSource u ∈ sourceFiniteGapLocus (by simp) (by norm_num)) : ℝ → ℂ :=
  (sourceFiniteGapPhysicalPair (by simp) (by norm_num) (hillMiuraRealSource u) hf).1

theorem sourceFiniteGapPhysicalPair_hillMiura (u : PeriodOneRealL2)
    (hf : hillMiuraRealSource u ∈ sourceFiniteGapLocus (by simp) (by norm_num)) :
    sourceFiniteGapPhysicalPair (by simp) (by norm_num) (hillMiuraRealSource u) hf=
      (hillMiuraFiniteGapProfile u hf,hillMiuraFiniteGapProfile u hf) := by
  apply Prod.ext
  · rfl
  · change periodOneSynthesis _=periodOneSynthesis _
    apply congrArg periodOneSynthesis
    ext k
    simp only [hillMiuraRealSource,hillMiuraDiagonal_snd,hillMiuraDiagonal_fst]

theorem contDiff_hillMiuraFiniteGapProfile (u : PeriodOneRealL2)
    (hf : hillMiuraRealSource u ∈ sourceFiniteGapLocus (by simp) (by norm_num)) :
    ContDiff ℝ ∞ (hillMiuraFiniteGapProfile u hf) :=
  (contDiff_sourceFiniteGapPhysicalPair (by simp) (by norm_num) (hillMiuraRealSource u) hf).1

theorem periodic_hillMiuraFiniteGapProfile (u : PeriodOneRealL2)
    (hf : hillMiuraRealSource u ∈ sourceFiniteGapLocus (by simp) (by norm_num)) :
    Function.Periodic (hillMiuraFiniteGapProfile u hf) 1 :=
  (periodic_sourceFiniteGapPhysicalPair (by simp) (by norm_num) (hillMiuraRealSource u) hf).1

theorem periodOneCoefficient_hillMiuraFiniteGapProfile (u : PeriodOneRealL2)
    (hf : hillMiuraRealSource u ∈ sourceFiniteGapLocus (by simp) (by norm_num)) (n : ℤ) :
    periodOneCoefficient (hillMiuraFiniteGapProfile u hf) n=u.val n := by
  simpa only [hillMiuraFiniteGapProfile,hillMiuraRealSource,hillMiuraDiagonal_fst] using!
    (periodOneCoefficient_sourceFiniteGapPhysicalPair (by simp) (by norm_num) (hillMiuraRealSource u) hf n).1

theorem sourceFiniteGapNLSHamiltonian_hillMiura_eq_classical (u : PeriodOneRealL2)
    (hf : hillMiuraRealSource u ∈ sourceFiniteGapLocus (by simp) (by norm_num)) (k : ℕ) :
    sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) (hillMiuraRealSource u) hf k=
      classicalNLSHamiltonian (hillMiuraFiniteGapProfile u hf) (hillMiuraFiniteGapProfile u hf) k := by
  rw [sourceFiniteGapNLSHamiltonian,sourceFiniteGapPhysicalPair_hillMiura]

theorem integral_sq_hillMiuraFiniteGapProfile (u : PeriodOneRealL2)
    (hf : hillMiuraRealSource u ∈ sourceFiniteGapLocus (by simp) (by norm_num)) :
    (∫ x in (0:ℝ)..1, (hillMiuraFiniteGapProfile u hf x)^2)=((‖u.val‖^2:ℝ):ℂ) := by
  have hm := sourceFiniteGapNLSHamiltonian_one (by simp) (by norm_num) (hillMiuraRealSource u) hf
  rw [sourceFiniteGapNLSHamiltonian_hillMiura_eq_classical,classicalNLSHamiltonian_one] at hm
  have hmass : (∑' k : ℤ, (hillMiuraRealSource u).val.fst k*(hillMiuraRealSource u).val.snd (-k))=
      ((‖u.val‖^2:ℝ):ℂ) := by
    change (∑' k : ℤ, (hillMiuraDiagonal u.val).fst k*(hillMiuraDiagonal u.val).snd (-k))=_
    rw [hillMiuraDiagonal_fst,hillMiuraDiagonal_snd,← Coeff.oppositeHilbertPairing_apply]
    exact Coeff.oppositeHilbertPairing_self_eq_norm_sq _ u.property
  rw [hmass] at hm
  simpa only [pow_two] using hm

theorem periodOneCoefficient_miura_hillMiuraFiniteGapProfile (u : PeriodOneRealL2)
    (hf : hillMiuraRealSource u ∈ sourceFiniteGapLocus (by simp) (by norm_num)) (n : ℤ) :
    periodOneCoefficient (NLS.MKdV.miuraPotential (hillMiuraFiniteGapProfile u hf)) n=
      (periodOneMiura u.val).val n := by
  let f := hillMiuraFiniteGapProfile u hf
  have hs := contDiff_hillMiuraFiniteGapProfile u hf
  have hp := periodic_hillMiuraFiniteGapProfile u hf
  change periodOneCoefficient (deriv f+(fun x => (f x)^2)) n=_
  have hpow : (fun x => (f x)^2)=f*f := by funext x; exact pow_two _
  rw [hpow]
  have ha := periodOneCoefficient_add (deriv f) (f*f)
    (contDiff_infty_iff_deriv.mp hs).2.continuous (hs.mul hs).continuous n
  rw [periodOneCoefficient_deriv_of_smooth_periodic f hs hp,
    periodOneCoefficient_mul_of_smooth_periodic f f hs hs hp hp] at ha
  simpa only [f,periodOneCoefficient_hillMiuraFiniteGapProfile,periodOneMiura_apply] using! ha

end NLS.KdV
