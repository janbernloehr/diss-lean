import NLS.KdV.HillMiuraZeroFrequencyTrace
import NLS.KdV.HillMiuraCoefficientContinuity

/-! For a real diagonal L² lift, zero belongs to the actual Dirac spectrum
exactly when its raw mean vanishes. Equivalently, its central endpoint
pair collapses at zero. The original endpoint indices are retained. -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.KdV

theorem periodOneRealL2_zero_eq_re (u : PeriodOneRealL2) :
    u.val 0 = ((u.val 0).re : ℂ) := by
  apply (Complex.conj_eq_iff_re.mp ?_).symm
  simpa only [neg_zero] using (u.property 0).symm

theorem hillMiuraFrequencyTrace_zero_real (u : PeriodOneRealL2) :
    hillMiuraFrequencyTrace u.val 0 = (2*Real.cosh (u.val 0).re : ℝ) := by
  rw [hillMiuraFrequencyTrace_zero,periodOneRealL2_zero_eq_re,← Complex.ofReal_cosh]
  push_cast
  rfl

theorem hillMiura_zero_mem_spectrum_iff_mean_zero (u : PeriodOneRealL2) :
    (0:ℂ) ∈ periodicSpectrum (by simp) (periodOnePotential (hillMiuraDiagonal u.val)) ↔
      u.val 0 = 0 := by
  have hs : (hillMiuraFrequencyTrace u.val 0)^2=4 ↔
      (0:ℂ) ∈ periodicSpectrum (by simp) (periodOnePotential (hillMiuraDiagonal u.val)) :=
    canonicalDiscriminant_sq_eq_four_iff _ (periodOnePotential_mem _) 0
  rw [← hs,hillMiuraFrequencyTrace_zero_real]
  constructor
  · intro he
    have hr : (2*Real.cosh (u.val 0).re)^2=4 := by exact_mod_cast he
    have h0 : (u.val 0).re=0 := by
      by_contra hn
      have hp := Real.one_lt_cosh.mpr hn
      nlinarith
    rw [periodOneRealL2_zero_eq_re,h0,Complex.ofReal_zero]
  · intro he
    simp only [he,zero_re,Real.cosh_zero,mul_one]
    norm_num

theorem hillMiura_central_right_zero_of_mem_spectrum (u : PeriodOneRealL2)
    (hz : (0:ℂ) ∈ periodicSpectrum (by simp) (periodOnePotential (hillMiuraDiagonal u.val))) :
    hillMiuraDiracRight u.val 0=0 := by
  apply Complex.ext
  · apply le_antisymm
    · exact le_of_not_gt (fun hp => zero_not_mem_hillMiura_spectrum_of_central_right_pos u hp hz)
    · exact (hillMiura_gap_zero_contains_zero u).2
  · exact (hillMiuraDiracPair_real u 0).2


theorem hillMiura_central_right_zero_iff_mean_zero (u : PeriodOneRealL2) :
    hillMiuraDiracRight u.val 0=0 ↔ u.val 0=0 := by
  constructor
  · intro he
    apply (hillMiura_zero_mem_spectrum_iff_mean_zero u).mp
    have hs := (canonicalPeriodicEndpoints_mem_spectrum (by simp) (by norm_num)
      (periodOnePotential (hillMiuraDiagonal u.val)) (periodOnePotential_mem _) 0).2
    change hillMiuraDiracRight u.val 0 ∈ _ at hs
    rwa [he] at hs
  · intro he
    exact hillMiura_central_right_zero_of_mem_spectrum u
      ((hillMiura_zero_mem_spectrum_iff_mean_zero u).mpr he)

theorem hillMiura_central_gap_collapsed_iff_mean_zero (u : PeriodOneRealL2) :
    hillMiuraDiracLeft u.val 0=hillMiuraDiracRight u.val 0 ↔ u.val 0=0 := by
  have hr := (hillMiuraDiracPair_neg u.val).1 0
  simp only [neg_zero] at hr
  rw [← hillMiura_central_right_zero_iff_mean_zero]
  constructor
  · intro he
    have h := he.symm.trans hr
    have hre := congrArg Complex.re h
    have him := congrArg Complex.im h
    apply Complex.ext <;> simp only [zero_re,zero_im,neg_re,neg_im] at * <;> linarith
  · intro he
    rw [hr,he,neg_zero]

theorem hillMiura_central_right_pos_iff_mean_ne_zero (u : PeriodOneRealL2) :
    0 < (hillMiuraDiracRight u.val 0).re ↔ u.val 0 ≠ 0 := by
  have hn := (hillMiura_gap_zero_contains_zero u).2
  have hi := (hillMiuraDiracPair_real u 0).2
  constructor
  · intro hp hm
    have he := (hillMiura_central_right_zero_iff_mean_zero u).mpr hm
    rw [he,zero_re] at hp
    exact lt_irrefl 0 hp
  · intro hm
    apply lt_of_le_of_ne hn
    intro he
    apply hm
    apply (hillMiura_central_right_zero_iff_mean_zero u).mp
    exact Complex.ext he.symm hi

end NLS.KdV
