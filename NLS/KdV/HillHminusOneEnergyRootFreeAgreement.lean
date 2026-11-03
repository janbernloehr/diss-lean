import NLS.KdV.HillHminusOneRealSpectralExclusion
import NLS.ZakharovShabat.SourcePsiFree

/-! # The actual energy root has the original free normalization

A high real band compares the actual canonical root of a shifted Miura
chart at zero with the literal zero-source NLS product. Connected-domain
uniqueness then identifies it with the original free-normalized Hill
continuation root on their full common energy domain.
-/
noncomputable section
open Set Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV

@[simp] theorem hillHminusContinuedRoot_base_sine (energy : ℂ) :
    hillHminusContinuedRoot (energy,0) = -2*I*sin (sqrt energy) := by
  change hillHminusSourceFamily.root (energy,0) = _
  rw [TracePrimitiveFamily.root_base]
  change 2*sinh (-I*sqrt energy) = _
  rw [neg_mul,sinh_neg,mul_comm I,sinh_mul_I]
  ring

namespace HillHminusMiuraChart

theorem exists_real_energyRoot_free_value (C : HillHminusMiuraChart)
    (h0 : (0 : PeriodOneHminusOne) ∈ C.domain) (hc : C.energyShift.im = 0)
    (hr : IsRealType (CoeffPair.toMax 2 (C.criticalSource 0))) :
    ∃ energy : ℂ, energy.im = 0 ∧ energy ∈ C.energyRootDomain 0 ∧
      (energy,0) ∈ hillHminusContinuationDomain ∧
      C.energyRoot 0 energy = hillHminusContinuedRoot (energy,0) := by
  obtain ⟨N,_,hN⟩ := exists_high_shifted_real_band (by simp) (by norm_num)
    (C.criticalSource 0) C.energyShift hc
  obtain ⟨M,_,hM⟩ := exists_high_shifted_real_band (by simp) (by norm_num)
    (0 : CoeffPair 2) 0 (by simp)
  let n := max N M
  let w : ℂ := ((Real.pi*(n:ℝ)+Real.pi/2 : ℝ):ℂ)
  let z := sqrt (w^2+C.energyShift)
  have hw : 0 < w.re := by
    change 0 < Real.pi*(n:ℝ)+Real.pi/2
    positivity
  obtain ⟨hz,hzi,hzb⟩ := hN n (le_max_left _ _)
  have hvb := (hM n (le_max_right _ _)).2.2
  change (sqrt (w^2+0)).re ∈ _ at hvb
  rw [add_zero,sqrt_sq_of_re_pos w hw] at hvb
  have hzreal : (z.re:ℂ) = z := Complex.ext rfl (by simpa only [ofReal_im] using hzi.symm)
  have hwreal : (w.re:ℂ) = w := by simp [w]
  have hzdom := sourceRealBand_subset_rootDomain (by simp) (by norm_num)
    (C.criticalSource 0) hr (n:ℤ) z.re hzb
  have hDC : w^2 ∈ C.energyRootDomain 0 := by
    refine ⟨?_,?_⟩
    · rw [← sq_sqrt (w^2+C.energyShift)]
      exact square_mem_slitPlane_of_re_pos z hz
    · rw [hzreal] at hzdom
      exact hzdom
  have hsignC := sourceCanonicalRoot_realBand_sign (by simp) (by norm_num)
    (C.criticalSource 0) hr (n:ℤ) z.re hzb
  have hsign0 := sourceCanonicalRoot_realBand_sign (by simp) (by norm_num)
    (0 : CoeffPair 2) (by simp) (n:ℤ) w.re hvb
  rw [hzreal] at hsignC
  change (C.energyRoot 0 (w^2)).re = 0 ∧
    (-1:ℝ)^(n:ℤ).natAbs*(C.energyRoot 0 (w^2)).im < 0 at hsignC
  rw [hwreal,sourceCanonicalRoot_zero_source_eq_free_sine (by simp) (by norm_num) 0] at hsign0
  have hf : hillHminusContinuedRoot (w^2,0) = -2*I*sin w := by
    rw [hillHminusContinuedRoot_base_sine,sqrt_sq_of_re_pos w hw]
  have hne : hillHminusRadicand 0 (w^2) ≠ 0 := by
    change hillHminusDiscriminant 0 (w^2)^2-4 ≠ 0
    rw [← C.energyRoot_sq 0 h0 _ hDC]
    exact pow_ne_zero _ (C.energyRoot_ne_zero 0 _ hDC)
  have hD0 : (w^2,(0 : PeriodOneHminusOne)) ∈ hillHminusContinuationDomain := by
    rw [mem_hillHminusContinuationDomain_iff]
    exact ⟨square_mem_slitPlane_of_re_pos w hw,fun r _ => by simpa only [smul_zero] using hne⟩
  have hs : C.energyRoot 0 (w^2)^2 = hillHminusContinuedRoot (w^2,0)^2 := by
    rw [C.energyRoot_sq 0 h0 _ hDC,hillHminusContinuedRoot_sq _ hD0]
    rfl
  refine ⟨w^2,by simp [w,pow_two],hDC,hD0,?_⟩
  rcases eq_or_eq_neg_of_sq_eq_sq _ _ hs with h | h
  · exact h
  · rw [h,hf,neg_im,mul_neg] at hsignC
    linarith [hsignC.2,hsign0.2]

theorem energyRoot_eq_continuedRoot_at_zero (C : HillHminusMiuraChart)
    (h0 : (0 : PeriodOneHminusOne) ∈ C.domain) (hc : C.energyShift.im = 0)
    (hr : IsRealType (CoeffPair.toMax 2 (C.criticalSource 0))) :
    EqOn (C.energyRoot 0) (fun energy => hillHminusContinuedRoot (energy,0))
      (C.energyRootDomain 0 ∩ {energy | (energy,0) ∈ hillHminusContinuationDomain}) := by
  obtain ⟨energy,hi,hC,hH,hvalue⟩ := C.exists_real_energyRoot_free_value h0 hc hr
  obtain ⟨hCo,hCa⟩ := C.energyRoot_spectral_real 0 hr
  have hHo : IsOpen {energy : ℂ | (energy,(0 : PeriodOneHminusOne)) ∈ hillHminusContinuationDomain} :=
    isOpen_hillHminusContinuationDomain.preimage (continuous_id.prodMk continuous_const)
  have hHa : AnalyticOnNhd ℂ (fun energy => hillHminusContinuedRoot (energy,0))
      {energy : ℂ | (energy,0) ∈ hillHminusContinuationDomain} := by
    intro energy he
    exact (analyticOnNhd_hillHminusContinuedRoot _ he).comp
      (f := fun energy : ℂ => (energy,(0 : PeriodOneHminusOne)))
      (analyticAt_id.prod analyticAt_const)
  have hconn := isPreconnected_of_contains_nonreal
    (D := C.energyRootDomain 0 ∩ {energy | (energy,0) ∈ hillHminusContinuationDomain})
    (fun z hz => ⟨C.nonreal_mem_energyRootDomain 0 hc hr z hz,
      nonreal_mem_hillHminusContinuationDomain 0 periodOneHminusConjugation_zero z hz⟩)
    ⟨hC,hH⟩ hi
  have hsq : ∀ᶠ z in 𝓝 energy,
      C.energyRoot 0 z ^ 2 = hillHminusContinuedRoot (z,0)^2 := by
    filter_upwards [(hCo.inter hHo).mem_nhds ⟨hC,hH⟩] with z hz
    rw [C.energyRoot_sq 0 h0 _ hz.1,hillHminusContinuedRoot_sq _ hz.2]
    rfl
  have hagree := eventuallyEq_of_sq_eq_of_continuousAt _ _ energy
    (hCa energy hC).continuousAt (hHa energy hH).continuousAt hvalue
    (hillHminusSourceFamily.root_ne_zero _ hH) hsq
  exact (hCa.mono inter_subset_left).eqOn_of_preconnected_of_eventuallyEq
    (hHa.mono inter_subset_right) hconn ⟨hC,hH⟩ hagree

end HillHminusMiuraChart
end NLS.KdV
