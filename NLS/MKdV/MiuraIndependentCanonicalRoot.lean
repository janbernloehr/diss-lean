import NLS.MKdV.MiuraCanonicalHillSheets
import NLS.MKdV.MiuraHillDirichletPositivity
import NLS.KdV.HillEnergyRootIdentification

/-! # The independent normalized Hill root and the physical Miura root

Connectedness and the actual first-band signs fix the square-root sign.
The independent Abelian-period root therefore agrees with the physical
Miura root on the complete original Hill real-cut domain.
-/
noncomputable section
open Set Complex Filter Topology
open NLS.ZakharovShabat NLS.KdV NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem miuraHillRealCutDomain_subset_gapComplement (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) :
    hillL2RealCutDomain (realSobolevMiuraHillPotential a ha).val
      (realSobolevMiuraHillPotential a ha).property.1
      (realSobolevMiuraHillPotential a ha).property.2 ⊆ miuraHillGapComplement a ha := by
  intro E hE
  constructor
  · intro hi
    rcases hE with hnon | ⟨m,hband⟩
    · exact (hnon hi).elim
    · have hle := monotone_miuraHillLabels a ha (show 0 ≤ 2*m by omega)
      exact hle.trans_lt hband.1
  · intro n hn hi hgap
    rcases hE with hnon | ⟨m,hband⟩
    · exact hnon hi
    · change E.re ∈ Ioo (miuraHillLabels a ha (2*m)) (miuraHillLabels a ha (2*m+1)) at hband
      by_cases hnm : n ≤ m
      · have hle := monotone_miuraHillLabels a ha (show 2*n ≤ 2*m by omega)
        linarith [hband.1,hgap.2]
      · have hle := monotone_miuraHillLabels a ha (show 2*m+1 ≤ 2*n-1 by omega)
        linarith [hband.2,hgap.1]

theorem hillEnergyCanonicalRootProduct_eq_canonicalMiuraHillRoot (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) :
    let q := realSobolevMiuraHillPotential a ha
    EqOn (hillEnergyCanonicalRootProduct q.val q.property.1 q.property.2)
      (canonicalMiuraHillRoot a) (hillL2RealCutDomain q.val q.property.1 q.property.2) := by
  let q := realSobolevMiuraHillPotential a ha
  have hsub := miuraHillRealCutDomain_subset_gapComplement a ha
  have hsq (E : ℂ) (hE : E ∈ hillL2RealCutDomain q.val q.property.1 q.property.2) :
      (hillEnergyCanonicalRootProduct q.val q.property.1 q.property.2 E)^2 =
        (canonicalMiuraHillRoot a E)^2 := by
    rw [hillEnergyCanonicalRootProduct_sq_eq_radicand q.val q.property.1 q.property.2 E hE,
      canonicalMiuraHillRoot_sq a ha E (hsub hE)]
    rw [realSobolevMiuraHillPotential_toCoeff]
  let x := ((miuraNLSRight a 0).re+(miuraNLSLeft a 1).re)/2
  have hbetween := miuraNLSEndpoints_between a ha (show (0 : ℤ) < 1 by norm_num)
  have hx : x ∈ Ioo (miuraNLSRight a 0).re (miuraNLSLeft a 1).re := by
    dsimp only [x]
    constructor <;> linarith
  have hxpos : 0 < x := (miuraNLSRight_zero_nonnegative a).trans_lt hx.1
  have hleft : miuraHillLabels a ha 1 = (miuraNLSLeft a 1).re^2 := by
    simpa only [Nat.mul_one,Nat.reduceSub,Nat.cast_one] using miuraHillLabels_left a ha 1 (by norm_num)
  have hxband : x^2 ∈ Ioo (hillRealLabels q.val q.property.1 q.property.2 0)
      (hillRealLabels q.val q.property.1 q.property.2 1) := by
    change x^2 ∈ Ioo (miuraHillLabels a ha 0) (miuraHillLabels a ha 1)
    rw [miuraHillLabels_ground a ha,hleft]
    constructor <;> nlinarith [miuraNLSRight_zero_nonnegative a,hx.1,hx.2]
  have hxcut : ((x : ℂ)^2) ∈ hillL2RealCutDomain q.val q.property.1 q.property.2 := by
    apply Or.inr
    refine ⟨0,?_⟩
    simpa only [← ofReal_pow,ofReal_re,Nat.mul_zero,zero_add] using hxband
  have he : hillEnergyCanonicalRootProduct q.val q.property.1 q.property.2 ((x : ℂ)^2) =
      canonicalMiuraHillRoot a ((x : ℂ)^2) := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hsq _ hxcut) with he | he
    · exact he
    · have hneg := hillEnergyCanonicalRootProduct_im_neg_first_band q.val q.property.1 q.property.2 (x^2) hxband
      have hphysical := (canonicalMiuraHillRoot_firstBand_sign a ha x hx).2
      have him := congrArg Complex.im he
      rw [ofReal_pow] at hneg
      simp only [mul_re,I_re,I_im,zero_mul,one_mul,zero_sub] at hphysical
      simp only [neg_im] at him
      linarith
  exact (isPreconnected_hillL2RealCutDomain q.val q.property.1 q.property.2).eq_of_sq_eq
    (analyticOnNhd_hillEnergyCanonicalRootProduct q.val q.property.1 q.property.2).continuousOn
    ((analyticOnNhd_canonicalMiuraHillSheets a ha).1.continuousOn.mono hsub) hsq
    (fun hE => canonicalMiuraHillRoot_ne_zero a ha _ (hsub hE)) hxcut he

end NLS.MKdV
