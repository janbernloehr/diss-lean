import NLS.MKdV.MiuraL2HillDiscriminant
import NLS.KdV.HillCanonicalRealLabels
import NLS.ZakharovShabat.PeriodicEndpointRootCounts

/-! # The physical Miura Hill spectrum inside the original NLS spectrum

The Hill potential is the actual H¹-to-L² Miura map. The independently
constructed H² Hill operator and the original ZS operator have equivalent
characteristic equations at squared energy, with analytic multiplicities
preserved away from zero. Reality of the NLS spectrum also proves the
nonnegativity of the whole Miura Hill characteristic zero set.
-/
noncomputable section
open Set Complex NLS.ZakharovShabat NLS.KdV
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

def sobolevMiuraWeightedPotential (a : ScalarDomain 2) : WeightedCoeff SpectralWeight.one.toWeight 2 :=
  (WeightedCoeff.weightIsometry SpectralWeight.one.toWeight 2).symm (sobolevMiuraHillPotential a)

@[simp] theorem toCoeff_sobolevMiuraWeightedPotential (a : ScalarDomain 2) :
    SpectralWeight.one.toCoeff (sobolevMiuraWeightedPotential a) = sobolevMiuraHillPotential a := by
  ext k
  rw [SpectralWeight.toCoeff_apply]
  change sobolevMiuraHillPotential a k/(SpectralWeight.one k : ℂ) = sobolevMiuraHillPotential a k
  rw [SpectralWeight.one_apply,ofReal_one,div_one]

theorem hillL2Discriminant_miura_eq_canonical (a : ScalarDomain 2) (z : ℂ) :
    hillL2Discriminant (sobolevMiuraHillPotential a) (z^2) =
      canonicalDiscriminant (by simp) (periodOnePotential (sobolevSourceInclusion (a,a))) z := by
  apply (hillL2Discriminant_miura a (z^2)).trans
  simpa only [miuraDiagonalSource_periodOneMiuraCurve] using
    (canonicalDiscriminant_miuraDiagonalSource (periodOneMiuraCurve a) z).symm

/-- Actual H² Hill eigenvectors are detected by the original ZS periodic
spectrum. Complex H¹ inputs and zero frequency are included. -/
theorem miuraHill_eigenvector_iff_ZS (a : ScalarDomain 2) (z : ℂ) :
    (∃ f : HillSobolevDomain, f ≠ 0 ∧
      hillOperator (sobolevMiuraHillPotential a) f = z^2 • hillDomainToL2 f) ↔
      z ∈ periodicSpectrum (by simp) (periodOnePotential (sobolevSourceInclusion (a,a))) := by
  have h := hill_eigenvector_iff_l2Discriminant (sobolevMiuraWeightedPotential a) (by
    rw [toCoeff_sobolevMiuraWeightedPotential]
    exact sobolevMiuraHillPotential_even a) (z^2)
  simp only [toCoeff_sobolevMiuraWeightedPotential] at h
  rw [hillL2Discriminant_miura_eq_canonical] at h
  exact h.trans (canonicalDiscriminant_sq_eq_four_iff _ (periodOnePotential_mem _) z)

theorem analyticOrderNatAt_miuraHillRadicand_sq (a : ScalarDomain 2) (z : ℂ) :
    analyticOrderNatAt (fun w : ℂ => hillL2Radicand (sobolevMiuraHillPotential a) (w^2)) z =
      periodicAlgebraicMultiplicity (by simp) (periodOnePotential (sobolevSourceInclusion (a,a))) z := by
  have he : (fun w : ℂ => hillL2Radicand (sobolevMiuraHillPotential a) (w^2)) =
      canonicalPeriodicProduct (by simp) (periodOnePotential (sobolevSourceInclusion (a,a))) := by
    funext w
    rw [canonicalPeriodic_eq_discriminant_sq_sub_four _ (periodOnePotential_mem _)]
    exact congrArg (fun d : ℂ => d^2-4) (hillL2Discriminant_miura_eq_canonical a w)
  rw [he]
  exact analyticOrderNatAt_canonicalPeriodicProduct (by simp) (by norm_num) _ z

theorem analyticOrderNatAt_miuraHillRadicand_energy (a : ScalarDomain 2) (z : ℂ) (hz : z ≠ 0) :
    analyticOrderNatAt (hillL2Radicand (sobolevMiuraHillPotential a)) (z^2) =
      periodicAlgebraicMultiplicity (by simp) (periodOnePotential (sobolevSourceInclusion (a,a))) z := by
  have hd : HasDerivAt (fun w : ℂ => w^2) (2*z) z := by simpa using! (hasDerivAt_id z).pow 2
  have hg : AnalyticAt ℂ (fun w : ℂ => w^2) z := analyticAt_id.pow 2
  have hdn : deriv (fun w : ℂ => w^2) z ≠ 0 := by
    rw [hd.deriv]
    exact mul_ne_zero (by norm_num) hz
  have he := analyticOrderAt_comp_of_deriv_ne_zero
    (f := hillL2Radicand (sobolevMiuraHillPotential a)) hg hdn
  have hn := congrArg ENat.toNat he
  change analyticOrderNatAt (fun w : ℂ => hillL2Radicand (sobolevMiuraHillPotential a) (w^2)) z =
    analyticOrderNatAt (hillL2Radicand (sobolevMiuraHillPotential a)) (z^2) at hn
  rw [← hn]
  exact analyticOrderNatAt_miuraHillRadicand_sq a z

/-- The energy-zero ramification is included with its exact factor two. -/
theorem miuraHillRadicand_zero_multiplicity (a : ScalarDomain 2) :
    periodicAlgebraicMultiplicity (by simp) (periodOnePotential (sobolevSourceInclusion (a,a))) 0 =
      2*analyticOrderNatAt (hillL2Radicand (sobolevMiuraHillPotential a)) 0 := by
  have hF : AnalyticAt ℂ (hillL2Radicand (sobolevMiuraHillPotential a)) ((0 : ℂ)^2) := by
    simpa only [zero_pow (by decide : 2 ≠ 0)] using
      analyticOnNhd_hillL2Radicand (sobolevMiuraHillPotential a) 0 (mem_univ _)
  have hg : AnalyticAt ℂ (fun w : ℂ => w^2) 0 := analyticAt_id.pow 2
  have he := hF.analyticOrderAt_comp hg
  have hpow : analyticOrderAt (fun w : ℂ => w^2) 0 = 2 := by
    have hi : AnalyticAt ℂ (id : ℂ → ℂ) 0 := analyticAt_id
    have h := analyticOrderAt_pow hi 2
    have hefun : (id : ℂ → ℂ)^2 = (fun w : ℂ => w^2) := by funext w; rfl
    rw [hefun] at h
    simpa using h
  have hn := congrArg ENat.toNat he
  simp only [zero_pow (by decide : 2 ≠ 0),sub_zero,hpow,ENat.toNat_mul,ENat.toNat_ofNat] at hn
  change analyticOrderNatAt (fun w : ℂ => hillL2Radicand (sobolevMiuraHillPotential a) (w^2)) 0 =
    analyticOrderNatAt (hillL2Radicand (sobolevMiuraHillPotential a)) 0*2 at hn
  rw [analyticOrderNatAt_miuraHillRadicand_sq] at hn
  simpa only [mul_comm] using hn

theorem miuraHillRadicand_root_nonnegative (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (μ : ℂ)
    (hμ : hillL2Radicand (sobolevMiuraHillPotential a) μ = 0) : μ.im = 0 ∧ 0 ≤ μ.re := by
  obtain ⟨z,rfl⟩ := IsAlgClosed.exists_pow_nat_eq μ (by norm_num : 0 < 2)
  rw [hillL2Radicand,hillL2Discriminant_miura_eq_canonical] at hμ
  have hs := (canonicalDiscriminant_sq_eq_four_iff _ (periodOnePotential_mem _) z).mp
    (sub_eq_zero.mp hμ)
  have hreal := isRealType_periodOnePotential (realDiagonalH1Source a ha).val
    (realDiagonalH1Source a ha).property
  have hi := periodicSpectrum_im_eq_zero_of_realType (by simp) _ hreal z hs
  constructor
  · simp only [pow_two,mul_im,hi,mul_zero,zero_mul,add_zero]
  · simpa only [pow_two,mul_re,hi,mul_zero,sub_zero] using mul_self_nonneg z.re

end NLS.MKdV
