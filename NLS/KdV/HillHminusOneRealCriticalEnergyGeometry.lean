import NLS.KdV.HillHminusOneRealMiuraCharts
import NLS.ComplexAnalysis.RightHalfPlaneSquareRoot
import NLS.ZakharovShabat.EvenRealCanonicalCriticalPoints
import NLS.ZakharovShabat.SourceCriticalPointsAnalytic

/-! # Complete simple critical energies for real rough Hill inputs

The canonical NLS critical sequence reflects exactly. Its positive half
descends to all and only the critical energies of the independent rough
Hill trace. The central frequency is a ramification point, not an extra
energy critical point. Every descended critical point is simple.
-/
noncomputable section
open Set Complex NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV
namespace HillHminusMiuraChart
variable (C : HillHminusMiuraChart) (q : PeriodOneHminusOne)
variable (hr : IsRealType (CoeffPair.toMax 2 (C.criticalSource q)))
include hr

theorem frequencyCritical_pos_real (n : ℕ+) :
    0 < (C.frequencyCritical q n).re ∧ (C.frequencyCritical q n).im = 0 := by
  refine ⟨?_,?_⟩
  · exact canonicalCriticalPoints_re_pos_of_discriminant_even_of_realType
      (by simp) (by norm_num) _ (periodOnePotential_mem _) (isRealType_periodOnePotential _ hr)
      (hillMiuraFrequencyTrace_even (C.lift q)) (n:ℤ) (by exact_mod_cast n.pos)
  · exact canonicalCriticalPoints_im_eq_zero (by simp) (by norm_num) _
      (periodOnePotential_mem _) (isRealType_periodOnePotential _ hr) (n:ℤ)

theorem shifted_zero_not_energy_critical (hq : q ∈ C.domain) :
    deriv (hillHminusDiscriminant q) (-C.energyShift) ≠ 0 := by
  have hzero := deriv_zero_of_even _ (hillMiuraFrequencyTrace_even (C.lift q))
  have hs := discriminant_second_derivative_ne_zero_at_critical_of_realType
    (by simp) (by norm_num) _ (periodOnePotential_mem _) (isRealType_periodOnePotential _ hr) 0 hzero
  have he := C.frequency_second_derivative_eq q hq 0
  simp only [zero_pow (by norm_num : (2:ℕ) ≠ 0),zero_mul,mul_zero,zero_sub,add_zero] at he
  intro h
  rw [h,mul_zero] at he
  exact hs he

theorem energyCritical_is_critical (hq : q ∈ C.domain) (n : ℕ+) :
    deriv (hillHminusDiscriminant q) (C.energyCritical q n) = 0 := by
  have h := canonicalCriticalPoints_is_critical (by simp) (by norm_num)
    (periodOnePotential (C.criticalSource q)) (periodOnePotential_mem _) (n:ℤ)
  change deriv (canonicalDiscriminant (by simp) (periodOnePotential (C.criticalSource q)))
    (C.frequencyCritical q n) = 0 at h
  rw [C.frequency_derivative_eq q hq] at h
  exact (mul_eq_zero.mp h).resolve_left
    (mul_ne_zero (by norm_num) (fun h => by
      have hp := (C.frequencyCritical_pos_real q hr n).1
      rw [h,zero_re] at hp
      exact (lt_irrefl _ hp)))

theorem energyCritical_simple (hq : q ∈ C.domain) (n : ℕ+) :
    deriv (deriv (hillHminusDiscriminant q)) (C.energyCritical q n) ≠ 0 := by
  have hz := canonicalCriticalPoints_is_critical (by simp) (by norm_num)
    (periodOnePotential (C.criticalSource q)) (periodOnePotential_mem _) (n:ℤ)
  have hs := discriminant_second_derivative_ne_zero_at_critical_of_realType
    (by simp) (by norm_num) _ (periodOnePotential_mem _) (isRealType_periodOnePotential _ hr)
    (C.frequencyCritical q n) hz
  rw [C.frequency_second_derivative_eq q hq] at hs
  change 2*deriv (hillHminusDiscriminant q) (C.energyCritical q n)+
    4*C.frequencyCritical q n^2*deriv (deriv (hillHminusDiscriminant q)) (C.energyCritical q n) ≠ 0 at hs
  rw [C.energyCritical_is_critical q hr hq n,mul_zero,zero_add] at hs
  intro h
  exact hs (by rw [h,mul_zero])

theorem energyCritical_exhaustive (hq : q ∈ C.domain) (energy : ℂ) :
    deriv (hillHminusDiscriminant q) energy = 0 ↔
      ∃ n : ℕ+, C.energyCritical q n = energy := by
  constructor
  · intro henergy
    let z := sqrt (energy+C.energyShift)
    have he : z^2-C.energyShift = energy := by dsimp only [z]; rw [sq_sqrt,add_sub_cancel_right]
    have hz : z ≠ 0 := by
      intro hz
      have he0 : energy = -C.energyShift := by simpa only [hz,zero_pow (by norm_num : (2:ℕ) ≠ 0),zero_sub] using he.symm
      exact C.shifted_zero_not_energy_critical q hr hq (he0 ▸ henergy)
    have hcrit : deriv (canonicalDiscriminant (by simp) (periodOnePotential (C.criticalSource q))) z = 0 := by
      rw [C.frequency_derivative_eq q hq,he,henergy,mul_zero]
    obtain ⟨k,hk⟩ := (canonicalCriticalPoints_exhaustive (by simp) (by norm_num)
      _ (periodOnePotential_mem _) z).mp hcrit
    have hk0 : k ≠ 0 := by
      intro hk0
      rw [hk0,canonicalCriticalPoints_zero_of_discriminant_even_of_realType
        (by simp) (by norm_num) _ (periodOnePotential_mem _) (isRealType_periodOnePotential _ hr)
        (hillMiuraFrequencyTrace_even (C.lift q))] at hk
      exact hz hk.symm
    rcases lt_or_gt_of_ne hk0 with hkn | hkp
    · let n : ℕ+ := ⟨(-k).toNat,by omega⟩
      have hn : (n:ℤ) = -k := Int.toNat_of_nonneg (neg_nonneg.mpr hkn.le)
      have hb : C.frequencyCritical q n = -z := by
        rw [frequencyCritical,hn,canonicalCriticalPoints_neg_of_discriminant_even_of_realType
          (by simp) (by norm_num) _ (periodOnePotential_mem _) (isRealType_periodOnePotential _ hr)
          (hillMiuraFrequencyTrace_even (C.lift q)),hk]
      exact ⟨n,by rw [energyCritical,hb,neg_sq]; exact he⟩
    · let n : ℕ+ := ⟨k.toNat,by omega⟩
      have hn : (n:ℤ) = k := Int.toNat_of_nonneg hkp.le
      have hb : C.frequencyCritical q n = z := by rw [frequencyCritical,hn,hk]
      exact ⟨n,by rw [energyCritical,hb]; exact he⟩
  · rintro ⟨n,rfl⟩
    exact C.energyCritical_is_critical q hr hq n

theorem energyCritical_im_eq_zero (hc : C.energyShift.im = 0) (n : ℕ+) :
    (C.energyCritical q n).im = 0 := by
  have hi := (C.frequencyCritical_pos_real q hr n).2
  simp only [energyCritical,sub_im,pow_two,mul_im,hi,hc,mul_zero,zero_mul,add_zero,sub_self]

theorem strictMono_energyCritical_re : StrictMono (fun n : ℕ+ => (C.energyCritical q n).re) := by
  intro n m hnm
  have hn := (C.frequencyCritical_pos_real q hr n).1
  have hni := (C.frequencyCritical_pos_real q hr n).2
  have hmi := (C.frequencyCritical_pos_real q hr m).2
  have horder := strictMono_canonicalCriticalPoints_re_of_realType (by simp) (by norm_num)
    (periodOnePotential (C.criticalSource q)) (periodOnePotential_mem _) (isRealType_periodOnePotential _ hr)
    (show (n:ℤ) < (m:ℤ) by exact_mod_cast hnm)
  change (C.frequencyCritical q n).re < (C.frequencyCritical q m).re at horder
  simp only [energyCritical,sub_re,pow_two,mul_re,hni,hmi,mul_zero,sub_zero]
  nlinarith

theorem analyticAt_energyCritical_of_realType (hq : q ∈ C.domain) (n : ℕ+) :
    AnalyticAt ℂ (fun p => C.energyCritical p n) q := by
  have h := (analyticAt_sourceCanonicalCriticalPoint_of_realType (by simp) (by norm_num)
    (n:ℤ) (C.criticalSource q) hr).comp (f := C.criticalSource) (C.analyticOnNhd_criticalSource q hq)
  exact (h.pow 2).sub analyticAt_const

end HillHminusMiuraChart

/-- Every actual rough Hill critical point is real and simple at every
physically real input, with no cutoff or open-gap restriction. -/
theorem hillHminus_critical_real_and_simple (q : PeriodOneHminusOne)
    (hq : periodOneHminusConjugation q = q) (energy : ℂ)
    (hcrit : deriv (hillHminusDiscriminant q) energy = 0) :
    energy.im = 0 ∧ deriv (deriv (hillHminusDiscriminant q)) energy ≠ 0 := by
  obtain ⟨C,hqC,_,hc,hr⟩ := exists_real_hillHminusMiuraChart q hq
  have hsource := (hr q hqC hq).2
  obtain ⟨j,hj⟩ := (C.energyCritical_exhaustive q hsource hqC energy).mp hcrit
  rw [← hj]
  exact ⟨C.energyCritical_im_eq_zero q hsource hc j,C.energyCritical_simple q hsource hqC j⟩

/-- One constructed actual chart precedes all real inputs, all energies
and all positive critical labels on its domain. -/
theorem exists_hillHminus_complete_real_critical_energies (q0 : PeriodOneHminusOne)
    (hq0 : periodOneHminusConjugation q0 = q0) :
    ∃ C : HillHminusMiuraChart, q0 ∈ C.domain ∧ 0 < C.energyShift.re ∧ C.energyShift.im = 0 ∧
      ∀ q ∈ C.domain, periodOneHminusConjugation q = q →
        StrictMono (fun j : ℕ+ => (C.energyCritical q j).re) ∧
        (∀ energy : ℂ, deriv (hillHminusDiscriminant q) energy = 0 ↔
          ∃ j : ℕ+, C.energyCritical q j = energy) ∧
        ∀ j : ℕ+, (C.energyCritical q j).im = 0 ∧
          deriv (hillHminusDiscriminant q) (C.energyCritical q j) = 0 ∧
          deriv (deriv (hillHminusDiscriminant q)) (C.energyCritical q j) ≠ 0 ∧
          AnalyticAt ℂ (fun p => C.energyCritical p j) q := by
  obtain ⟨C,hqC,hpos,hc,hr⟩ := exists_real_hillHminusMiuraChart q0 hq0
  refine ⟨C,hqC,hpos,hc,?_⟩
  intro q hq hreal
  have hs := (hr q hq hreal).2
  exact ⟨C.strictMono_energyCritical_re q hs,C.energyCritical_exhaustive q hs hq,
    fun j => ⟨C.energyCritical_im_eq_zero q hs hc j,C.energyCritical_is_critical q hs hq j,
      C.energyCritical_simple q hs hq j,C.analyticAt_energyCritical_of_realType q hs hq j⟩⟩

end NLS.KdV
