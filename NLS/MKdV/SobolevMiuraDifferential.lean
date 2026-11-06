import NLS.ComplexAnalysis.CommutativeBilinearSquare
import NLS.MKdV.SobolevMiuraPotential
import NLS.ZakharovShabat.PeriodOneSobolevProductPairing
import NLS.ZakharovShabat.SobolevPhysicalJets

/-! # The actual H¹-to-L² Miura derivative and its physical gradient transpose

The derivative is the period-one operator h' + 2*u*h. Its transpose on
an H² Hill gradient is -f' + 2*u*f, an actual H¹ gradient. Every Fourier
coefficient and the original unconjugated physical pairing are retained.
-/
noncomputable section
open NLS.Poisson
open Set Complex NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.MKdV

theorem sobolevMiuraUnitPotential_eq_product (a : ScalarDomain 2) :
    sobolevMiuraUnitPotential a = periodOneDerivative a+scalarInclusion (periodOneSobolevProduct a a) := by
  rw [scalarInclusion_periodOneSobolevProduct]
  rfl

def sobolevMiuraDifferential (a : ScalarDomain 2) : ScalarDomain 2 →L[ℂ] Coeff 2 :=
  periodOneDerivative+(2 : ℂ) • (scalarInclusion.comp (periodOneSobolevProduct a))

theorem hasFDerivAt_sobolevMiuraUnitPotential (a : ScalarDomain 2) :
    HasFDerivAt sobolevMiuraUnitPotential (sobolevMiuraDifferential a) a := by
  have hp := NLS.ComplexAnalysis.hasFDerivAt_commutative_bilinear_square
    periodOneSobolevProduct periodOneSobolevProduct_comm a
  have hd := periodOneDerivative.hasFDerivAt.add (scalarInclusion.hasFDerivAt.comp a hp)
  have he : (fun b => periodOneDerivative b+scalarInclusion (periodOneSobolevProduct b b)) =
      sobolevMiuraUnitPotential := funext (fun b => (sobolevMiuraUnitPotential_eq_product b).symm)
  change HasFDerivAt (fun b => periodOneDerivative b+scalarInclusion (periodOneSobolevProduct b b)) _ a at hd
  rw [he] at hd
  simpa only [ContinuousLinearMap.comp_smul,sobolevMiuraDifferential] using! hd

theorem fderiv_sobolevMiuraUnitPotential (a : ScalarDomain 2) :
    fderiv ℂ sobolevMiuraUnitPotential a = sobolevMiuraDifferential a :=
  (hasFDerivAt_sobolevMiuraUnitPotential a).fderiv

def sobolevHillTestInclusion : ScalarSobolev 2 →L[ℂ] ScalarDomain 2 :=
  hierarchySobolevToScalarDomain 2 (by omega)

def sobolevHillTestDerivative : ScalarSobolev 2 →L[ℂ] ScalarDomain 2 :=
  (hierarchySobolevToScalarDomain 1 le_rfl).comp (hierarchySobolevDerivative 2 1 (by omega))

theorem scalarInclusion_sobolevHillTestDerivative (f : ScalarSobolev 2) :
    scalarInclusion (sobolevHillTestDerivative f) = periodOneDerivative (sobolevHillTestInclusion f) := by
  ext n
  simp only [scalarInclusion_apply,periodOneDerivative_apply]
  change (hierarchySobolevToScalarDomain 1 le_rfl (hierarchySobolevDerivative 2 1 (by omega) f)).val n = _
  rw [hierarchySobolevToScalarDomain_apply,hierarchySobolevDerivative_apply]
  change _ = 2*I*(Real.pi : ℂ)*n*(hierarchySobolevToScalarDomain 2 (by omega) f).val n
  rw [hierarchySobolevToScalarDomain_apply]

def sobolevMiuraAdjoint (a : ScalarDomain 2) (f : ScalarSobolev 2) : ScalarDomain 2 :=
  -sobolevHillTestDerivative f+(2 : ℂ) • periodOneSobolevProduct a (sobolevHillTestInclusion f)

theorem sobolevMiuraDifferential_pairing (a h : ScalarDomain 2) (f : ScalarSobolev 2) :
    reflectedHilbertPairing (scalarInclusion (sobolevHillTestInclusion f)) (sobolevMiuraDifferential a h) =
      reflectedHilbertPairing (scalarInclusion (sobolevMiuraAdjoint a f)) (scalarInclusion h) := by
  change reflectedHilbertPairing (scalarInclusion (sobolevHillTestInclusion f))
    (periodOneDerivative h+(2 : ℂ) • scalarInclusion (periodOneSobolevProduct a h)) = _
  rw [map_add,map_smul,reflectedHilbertPairing_periodOneDerivative,
    reflectedHilbertPairing_sobolevProduct,← scalarInclusion_sobolevHillTestDerivative]
  change _ = reflectedHilbertPairing (scalarInclusion
    (-sobolevHillTestDerivative f+(2 : ℂ) • periodOneSobolevProduct a (sobolevHillTestInclusion f))) (scalarInclusion h)
  simp only [map_add,map_neg,map_smul,add_apply,neg_apply,smul_apply,smul_eq_mul]

/-- Pulling back an actual Hill cotangent gives this actual physical H¹
Miura gradient. No regularity of the pulled-back gradient is assumed. -/
theorem hasFDerivAt_sobolevMiura_pullback (F : Coeff 2 → ℂ) (a : ScalarDomain 2)
    (f : ScalarSobolev 2)
    (hF : HasFDerivAt F (reflectedHilbertPairing (scalarInclusion (sobolevHillTestInclusion f)))
      (sobolevMiuraUnitPotential a)) :
    HasFDerivAt (fun b => F (sobolevMiuraUnitPotential b))
      ((reflectedHilbertPairing (scalarInclusion (sobolevMiuraAdjoint a f))).comp scalarInclusion) a := by
  have hd := hF.comp a (hasFDerivAt_sobolevMiuraUnitPotential a)
  have he : (reflectedHilbertPairing (scalarInclusion (sobolevHillTestInclusion f))).comp
      (sobolevMiuraDifferential a) =
        (reflectedHilbertPairing (scalarInclusion (sobolevMiuraAdjoint a f))).comp scalarInclusion := by
    apply ContinuousLinearMap.ext
    intro h
    exact sobolevMiuraDifferential_pairing a h f
  rw [he] at hd
  simpa only [Function.comp_def] using! hd

end NLS.MKdV
