import NLS.KdV.HillFreeAbelianNormalization
import NLS.KdV.HillAbelianCircleIntegrability

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal

namespace NLS.KdV

variable
    (hq : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem hillFreeEnergy_ne_of_mem_cut (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ hillL2RealCutDomain 0 hq hr) : (freeHillValue n : ℂ) ≠ z := by
  intro he
  have hs := not_mem_hillGapSegment_of_mem_realCutDomain 0 hq hr z hz n hn
  apply hs
  rw [← he,(hillFreeGapEndpoints hq hr n hn).1]
  exact left_mem_segment ℝ _ _

theorem hillFreeAbelianNumerator_single_root_variation
    (n m : ℕ) (_hn : 1 ≤ n) (hm : 1 ≤ m) (hmn : m ≠ n)
    (t : ℝ) (z : ℂ) (hz : z ∈ hillL2RealCutDomain 0 hq hr) :
    hillAbelianNumeratorProduct
        (Function.update hillFreeGapRoot (m-1) (freeHillValue m+t)) n z =
      hillAbelianNumeratorProduct hillFreeGapRoot n z *
        (((freeHillValue m : ℂ)+(t : ℂ)-z)/((freeHillValue m : ℂ)-z)) := by
  have hdiff := sub_ne_zero.mpr (hillFreeEnergy_ne_of_mem_cut hq hr m hm z hz)
  have hp := ((multipliable_hillAbelianNumeratorFactors 0 hq hr hillFreeGapRoot
    (hillFreeGapRoot_mem_box hq hr) n z).hasProd).mul
    (hasProd_ite_eq (m-1)
      (((freeHillValue m : ℂ)+(t : ℂ)-z)/((freeHillValue m : ℂ)-z)))
  have he (k : ℕ) : hillAbelianNumeratorFactor hillFreeGapRoot n k z *
      (if k = m-1 then
        ((freeHillValue m : ℂ)+(t : ℂ)-z)/((freeHillValue m : ℂ)-z) else 1) =
      hillAbelianNumeratorFactor
        (Function.update hillFreeGapRoot (m-1) (freeHillValue m+t)) n k z := by
    by_cases hk : k = m-1
    · have hkm : k+1 = m := by omega
      simp only [hillAbelianNumeratorFactor,if_pos hk,
        hillGapRootEnergyFactor,Function.update_apply,hillFreeGapRoot,hkm,if_neg hmn,ofReal_add]
      field_simp
    · have hval : Function.update hillFreeGapRoot (m-1) (freeHillValue m+t) k =
          hillFreeGapRoot k := Function.update_of_ne hk _ _
      simp only [if_neg hk,mul_one,hillAbelianNumeratorFactor,hillGapRootEnergyFactor,hval]
  simp only [he] at hp
  exact hp.tprod_eq

theorem hillFreeAbelianQuotient_single_root_variation
    (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (hmn : m ≠ n)
    (t : ℝ) (z : ℂ) (hz : z ∈ hillL2RealCutDomain 0 hq hr) :
    hillAbelianPsiCandidate
        (Function.update hillFreeGapRoot (m-1) (freeHillValue m+t)) n z /
        hillEnergyCanonicalRootProduct 0 hq hr z =
      hillAbelianPsiCandidate hillFreeGapRoot n z / hillEnergyCanonicalRootProduct 0 hq hr z +
        ((t : ℂ)/((freeHillValue m : ℂ)-(freeHillValue n : ℂ))) *
          (hillAbelianPsiCandidate hillFreeGapRoot n z / hillEnergyCanonicalRootProduct 0 hq hr z -
            ((n : ℂ)/(m : ℂ)) *
              (hillAbelianPsiCandidate hillFreeGapRoot m z / hillEnergyCanonicalRootProduct 0 hq hr z)) := by
  have hmnE : (freeHillValue m : ℂ)-(freeHillValue n : ℂ) ≠ 0 := by
    apply sub_ne_zero.mpr
    exact ofReal_injective.ne (strictMono_freeHillValue.injective.ne hmn)
  have hnz := sub_ne_zero.mpr (hillFreeEnergy_ne_of_mem_cut hq hr n hn z hz)
  have hmz := sub_ne_zero.mpr (hillFreeEnergy_ne_of_mem_cut hq hr m hm z hz)
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hbase : hillAbelianPsiCandidate
      (Function.update hillFreeGapRoot (m-1) (freeHillValue m+t)) n z =
      hillAbelianPsiCandidate hillFreeGapRoot n z *
        (((freeHillValue m : ℂ)+(t : ℂ)-z)/((freeHillValue m : ℂ)-z)) := by
    unfold hillAbelianPsiCandidate
    rw [hillFreeAbelianNumerator_single_root_variation hq hr n m hn hm hmn t z hz]
    ring
  rw [hbase,mul_div_right_comm,hillFreeAbelianQuotient hq hr n hn z hz,
    hillFreeAbelianQuotient hq hr m hm z hz]
  field_simp
  ring

theorem hillFreeAbelianPeriod_single_root_variation
    (n m k : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (hk : 1 ≤ k) (hmn : m ≠ n) (t : ℝ) :
    hillAbelianCandidatePeriod 0 hq hr
      (Function.update hillFreeGapRoot (m-1) (freeHillValue m+t)) n k =
      hillAbelianCandidatePeriod 0 hq hr hillFreeGapRoot n k +
        ((t : ℂ)/((freeHillValue m : ℂ)-(freeHillValue n : ℂ))) *
          (hillAbelianCandidatePeriod 0 hq hr hillFreeGapRoot n k -
            ((n : ℂ)/(m : ℂ))*hillAbelianCandidatePeriod 0 hq hr hillFreeGapRoot m k) := by
  let A (j : ℕ) : ℂ → ℂ := fun z => hillAbelianPsiCandidate hillFreeGapRoot j z /
    hillEnergyCanonicalRootProduct 0 hq hr z
  let a : ℂ := (t : ℂ)/((freeHillValue m : ℂ)-(freeHillValue n : ℂ))
  let b : ℂ := (n : ℂ)/(m : ℂ)
  have hA (j : ℕ) := hillAbelianCandidate_circleIntegrable 0 hq hr hillFreeGapRoot
    (hillFreeGapRoot_mem_box hq hr) j k hk
  have hB : CircleIntegrable (fun z => b*A m z)
      (hillRealGapCenter 0 hq hr k : ℂ)
      (hillRealGapHalfLength 0 hq hr k + hillRealGapCollar 0 hq hr k) := by
    exact (hA m).const_smul (a := b)
  have hC : CircleIntegrable (fun z => a*(A n z-b*A m z))
      (hillRealGapCenter 0 hq hr k : ℂ)
      (hillRealGapHalfLength 0 hq hr k + hillRealGapCollar 0 hq hr k) := by
    exact ((hA n).sub hB).const_smul (a := a)
  have hR := add_nonneg (hillRealGapContour_geometry 0 hq hr k hk).1
    (hillRealGapContour_geometry 0 hq hr k hk).2.1.le
  have he : EqOn (fun z => hillAbelianPsiCandidate
      (Function.update hillFreeGapRoot (m-1) (freeHillValue m+t)) n z /
      hillEnergyCanonicalRootProduct 0 hq hr z)
      (fun z => A n z+a*(A n z-b*A m z))
      (sphere (hillRealGapCenter 0 hq hr k : ℂ)
        (hillRealGapHalfLength 0 hq hr k + hillRealGapCollar 0 hq hr k)) := by
    intro z hz
    exact hillFreeAbelianQuotient_single_root_variation hq hr n m hn hm hmn t z
      (hillRealGapContour_sphere_subset 0 hq hr k hk hz)
  unfold hillAbelianCandidatePeriod
  rw [circleIntegral.integral_congr hR he,circleIntegral.integral_add (hA n) hC,
    circleIntegral.integral_const_mul,circleIntegral.integral_sub (hA n) hB,
    circleIntegral.integral_const_mul]
  dsimp only [A,a,b]
  ring

end NLS.KdV
