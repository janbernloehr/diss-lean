import NLS.MKdV.L2QuasiHillZeroGauge
import NLS.KdV.HillMiuraL2PhysicalQuasi
import NLS.KdV.HillMiuraMinimalMeanZero
import NLS.KdV.HillMiuraPositiveGaps
import NLS.ZakharovShabat.CanonicalCriticalInterlacing
import NLS.ZakharovShabat.RealGapCharacterization
import NLS.ZakharovShabat.SourceIndexedActionAnalytic

/-! # Zero energy and the collapsed central gap of normalized Miura factors

The mean-zero condition constructs an actual periodic gauge at zero.
The original canonical spectral ordering then forces both central Dirac
endpoints to be zero. These statements apply to every real L2 factor,
without a smoothness or smallness condition.
-/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory
open scoped ENNReal ComplexConjugate
namespace NLS.KdV
open NLS.Fourier NLS.ZakharovShabat NLS.MKdV NLS.ComplexAnalysis

theorem hillMiuraFrequencyTrace_zero_eq_two (u : PeriodOneRealL2) (hm : u.val 0 = 0) :
    hillMiuraFrequencyTrace u.val 0 = 2 := by
  have hc : unitFourierCoefficient (unitL2SynthesisEquiv u.val) 0 = u.val 0 := by
    rw [unitFourierCoefficient_eq_intervalFourierCoefficient]
    exact unitL2SynthesisLinear_coefficient u.val 0
  simp only [unitFourierCoefficient,mul_zero,neg_zero,wave_zero,mul_one] at hc
  have ht := l2QuasiHillDiscriminant_zero_eq_two_of_real_meanZero
    (unitL2SynthesisEquiv u.val) (unitL2Synthesis_star_eq_self_of_real u.val u.property) (hc.trans hm)
  rw [←hillMiuraL2Discriminant_eq_physicalQuasi,hillMiuraL2Discriminant,Complex.sqrt_zero] at ht
  exact ht

/-- The actual indexed central gap collapses at zero for every normalized
real L2 Miura factor. Its collapse is a consequence, not a hypothesis. -/
theorem hillMiura_central_endpoints_eq_zero (u : PeriodOneRealL2) (hm : u.val 0 = 0) :
    canonicalPeriodicLeft (by simp) (by norm_num)
      (periodOnePotential (hillMiuraDiagonal u.val)) (periodOnePotential_mem _) 0 = 0 ∧
    canonicalPeriodicRight (by simp) (by norm_num)
      (periodOnePotential (hillMiuraDiagonal u.val)) (periodOnePotential_mem _) 0 = 0 := by
  let φ := periodOnePotential (hillMiuraDiagonal u.val)
  have hr : IsRealType φ := isRealType_periodOnePotential _ (hillMiuraRealSource u).property
  have hle := re_le_of_complexLexLE ((canonicalPeriodicEndpoints_spec
    (by simp) (by norm_num) φ (periodOnePotential_mem _)).2.1 0)
  have he : (canonicalPeriodicLeft (by simp) (by norm_num) φ (periodOnePotential_mem _) 0).re =
      (canonicalPeriodicRight (by simp) (by norm_num) φ (periodOnePotential_mem _) 0).re := by
    apply le_antisymm hle
    by_contra hn
    have hc := canonicalCriticalPoints_between_of_open_gap
      (by simp) (by norm_num) φ (periodOnePotential_mem _) hr 0 (lt_of_not_ge hn)
    rw [hillMiuraCanonicalCritical_zero,zero_re] at hc
    have hh := two_lt_norm_discriminant_of_mem_canonicalGap_interior
      (by simp) (by norm_num) φ (periodOnePotential_mem _) hr 0 0 hc
    change 2 < ‖hillMiuraFrequencyTrace u.val (0 : ℂ)‖ at hh
    rw [hillMiuraFrequencyTrace_zero_eq_two u hm] at hh
    norm_num at hh
  have hi := canonicalPeriodicEndpoints_im_eq_zero_of_realType
    (by simp) (by norm_num) φ (periodOnePotential_mem _) hr 0
  have hec := Complex.ext he (hi.1.trans hi.2.symm)
  have hcrit := canonicalCriticalPoints_eq_of_collapsed_gap
    (by simp) (by norm_num) φ (periodOnePotential_mem _) hr 0 hec
  rw [hillMiuraCanonicalCritical_zero] at hcrit
  exact ⟨hcrit.symm,hec.symm.trans hcrit.symm⟩

theorem hillMiura_central_real_action_eq_zero (u : PeriodOneRealL2) (hm : u.val 0 = 0) :
    sourceRealAction (by simp) (by norm_num) (hillMiuraDiagonal u.val)
      (hillMiuraRealSource u).property 0 = 0 := by
  apply (sourceRealAction_nonneg_and_eq_zero_iff_gap_zero
    (by simp) (by norm_num) (hillMiuraDiagonal u.val) (hillMiuraRealSource u).property 0).2.2.mpr
  rw [sourcePeriodicGapDisplacement_apply,canonicalPeriodicGap,
    (hillMiura_central_endpoints_eq_zero u hm).1,(hillMiura_central_endpoints_eq_zero u hm).2,sub_self]

theorem hillMiura_central_indexed_action_eq_zero (u : PeriodOneRealL2) (hm : u.val 0 = 0) :
    sourceIndexedAction (by simp) (by norm_num) 0 (hillMiuraDiagonal u.val) = 0 := by
  rw [sourceIndexedAction_eq_sourceRealAction (by simp) (by norm_num) 0
    (hillMiuraDiagonal u.val) (hillMiuraRealSource u).property]
  exact hillMiura_central_real_action_eq_zero u hm

theorem hillMiura_central_complex_action_eq_zero (u : PeriodOneRealL2) (hm : u.val 0 = 0) :
    sourceComplexAction (by simp) (by norm_num) 0 (hillMiuraDiagonal u.val) = 0 := by
  rw [sourceComplexAction_eq_sourceRealAction (by simp) (by norm_num) 0
    (hillMiuraDiagonal u.val) (hillMiuraRealSource u).property]
  exact hillMiura_central_real_action_eq_zero u hm

/-- Every actual normalized factor identifies the translated rough Hill
trace at its energy, including the zero-energy state map. -/
theorem hillHminusDiscriminant_neg_energy_eq_two (q : PeriodOneHminusOne)
    (u : PeriodOneRealL2) (e : ℝ) (hm : u.val 0 = 0)
    (hi : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (e : ℂ))) :
    hillHminusDiscriminant q (-(e : ℂ)) = 2 := by
  have ht := hillHminusDiscriminant_shifted_miura_square q u.val (e : ℂ) 0 hi
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0),zero_sub] at ht
  exact ht.trans (hillMiuraFrequencyTrace_zero_eq_two u hm)

end NLS.KdV
