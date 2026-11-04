import NLS.KdV.HillNativeCartesianOrigin
import NLS.SequenceSpaces.PositiveCartesianComplexification

/-! The ACTUAL signed complex action-angle sequence, with the original
sqrt-two convention and literal signed minus-half Sobolev weight. -/
noncomputable section
open Set Complex
namespace NLS.KdV

def hillHminusNativeComplexMap (q : PeriodOneHminusOne) :
    WeightedCoeff (Weight.signedSobolev (-1/2)) 2 :=
  WeightedCoeffPair.signedCartesianCLM (-1/2) (hillHminusNativeCartesianMap q)

theorem analyticOnNhd_hillHminusNativeComplexMap :
    AnalyticOnNhd ℂ hillHminusNativeComplexMap hillHminusActionAngleNativeDomain := by
  intro q hq
  exact ((WeightedCoeffPair.signedCartesianCLM (-1/2)).analyticAt _).comp
    (analyticOnNhd_hillHminusNativeCartesianMap q hq)

theorem hillHminusNativeComplexMap_positive (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusActionAngleNativeDomain) (n : ℕ+) :
    (hillHminusNativeComplexMap q).val ((n:ℕ):ℤ)=hillHminusActionAngleFactorMinus n q/(Real.sqrt 2:ℂ) := by
  have hn : (0:ℤ) < ((n:ℕ):ℤ) := by exact_mod_cast n.pos
  rw [hillHminusNativeComplexMap,WeightedCoeffPair.signedCartesianCLM_positive _ _ _ hn,
    (hillHminusNativeCartesianMap_positive q hq n).1,(hillHminusNativeCartesianMap_positive q hq n).2,
    (hillHminusActionAngle_factor_reconstruction n q).2]

theorem hillHminusNativeComplexMap_negative (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusActionAngleNativeDomain) (n : ℕ+) :
    (hillHminusNativeComplexMap q).val (-((n:ℕ):ℤ))=hillHminusActionAngleFactorPlus n q/(Real.sqrt 2:ℂ) := by
  have hn : (0:ℤ) < ((n:ℕ):ℤ) := by exact_mod_cast n.pos
  rw [hillHminusNativeComplexMap,WeightedCoeffPair.signedCartesianCLM_negative _ _ _ hn,
    (hillHminusNativeCartesianMap_positive q hq n).1,(hillHminusNativeCartesianMap_positive q hq n).2,
    (hillHminusActionAngle_factor_reconstruction n q).1]

theorem hillHminusNativeComplexMap_zero_mode (q : PeriodOneHminusOne) :
    (hillHminusNativeComplexMap q).val 0=0 :=
  WeightedCoeffPair.signedCartesianCLM_zero _ _

theorem hillHminusNativeComplexMap_action_identity (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusActionAngleNativeDomain) (n : ℕ+) :
    (hillHminusNativeComplexMap q).val ((n:ℕ):ℤ)*(hillHminusNativeComplexMap q).val (-((n:ℕ):ℤ))=
      hillHminusCanonicalAction n q := by
  rw [hillHminusNativeComplexMap_positive q hq n,hillHminusNativeComplexMap_negative q hq n,
    div_mul_div_comm]
  have hs : (Real.sqrt 2:ℂ)*(Real.sqrt 2:ℂ)=2 := by
    rw [← Complex.ofReal_mul,Real.mul_self_sqrt (by norm_num)]
    norm_num
  rw [hs,mul_comm (hillHminusActionAngleFactorMinus n q),hillHminusActionAngleFactor_product n q
    (hillHminusActionAngleEnergyDomain_subset (hillHminusActionAngleNativeDomain_subset hq)).1]
  ring

theorem hillHminusNativeComplexMap_conjugate_pair (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (n : ℕ+) :
    (hillHminusNativeComplexMap q).val (-((n:ℕ):ℤ))=
      (starRingEnd ℂ) ((hillHminusNativeComplexMap q).val ((n:ℕ):ℤ)) := by
  have hq := real_mem_hillHminusActionAngleNativeDomain q hr
  rw [hillHminusNativeComplexMap_negative q hq n,hillHminusNativeComplexMap_positive q hq n,
    hillHminusActionAngleFactor_conjugate_of_real n q hr,map_div₀,Complex.conj_ofReal,
    ]
  change _ = (starRingEnd ℂ) ((starRingEnd ℂ) (hillHminusActionAngleFactorPlus n q))/(Real.sqrt 2:ℂ)
  rw [Complex.conj_conj]


theorem hillHminusNativeComplexMap_real (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (k : ℤ) :
    (hillHminusNativeComplexMap q).val (-k)=(starRingEnd ℂ) ((hillHminusNativeComplexMap q).val k) := by
  by_cases hk : k=0
  · subst k
    simp only [neg_zero,hillHminusNativeComplexMap_zero_mode,map_zero]
  · by_cases hp : 0 < k
    · let n : ℕ+ := ⟨k.toNat,by omega⟩
      have hn : ((n:ℕ):ℤ)=k := Int.toNat_of_nonneg hp.le
      rw [← hn]
      exact hillHminusNativeComplexMap_conjugate_pair q hr n
    · let n : ℕ+ := ⟨(-k).toNat,by omega⟩
      have hn : -((n:ℕ):ℤ)=k := by
        have hn' : ((n:ℕ):ℤ) = -k := Int.toNat_of_nonneg (by omega)
        omega
      rw [← hn,neg_neg,hillHminusNativeComplexMap_conjugate_pair q hr n,Complex.conj_conj]

theorem hillHminusNativeComplexMap_zero : hillHminusNativeComplexMap 0=0 := by
  rw [hillHminusNativeComplexMap,hillHminusNativeCartesianMap_zero,map_zero]

end NLS.KdV
