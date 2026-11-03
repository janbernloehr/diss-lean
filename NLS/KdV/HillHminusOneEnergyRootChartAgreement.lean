import NLS.KdV.HillHminusOneMiuraEnergyRoot
import NLS.ZakharovShabat.SourceHighShiftedRealBand
import NLS.ZakharovShabat.SourceCanonicalRootRealBand
import NLS.ZakharovShabat.SourceCriticalRootRatioContourHomotopy
import NLS.ComplexAnalysis.NonrealConnectedDomain

/-! # Actual chart independence of the energy-root branch at real inputs

A common high real band fixes the sign using the actual canonical-root
normalization. The common domain contains the entire nonreal plane and
that real band point, so analytic uniqueness gives agreement everywhere
on the common energy domain. No branch agreement is assumed.
-/
noncomputable section
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV
namespace HillHminusMiuraChart

theorem energyRoot_spectral_real (C : HillHminusMiuraChart) (q : PeriodOneHminusOne)
    (hr : IsRealType (CoeffPair.toMax 2 (C.criticalSource q))) :
    IsOpen (C.energyRootDomain q) ∧ AnalyticOnNhd ℂ (C.energyRoot q) (C.energyRootDomain q) := by
  let S := {energy : ℂ | energy+C.energyShift ∈ slitPlane}
  let T : ℂ → ℂ := fun energy => sqrt (energy+C.energyShift)
  have hS : IsOpen S := isOpen_slitPlane.preimage (continuous_id.add continuous_const)
  have hs : AnalyticOnNhd ℂ T S := by
    intro energy he
    exact (differentiableOn_sqrt.analyticOnNhd isOpen_slitPlane _ he).comp
      (f := fun energy : ℂ => energy+C.energyShift) (analyticAt_id.add analyticAt_const)
  have ho := isOpen_sourceCanonicalRootDomain_of_realType (by simp) (by norm_num) (C.criticalSource q) hr
  refine ⟨hs.continuousOn.isOpen_inter_preimage hS ho,?_⟩
  intro energy he
  exact (sourceCanonicalRoot_analyticOnNhd (by simp) (by norm_num) (C.criticalSource q) _ he.2).comp
    (f := T) (hs energy he.1)

theorem nonreal_mem_energyRootDomain (C : HillHminusMiuraChart) (q : PeriodOneHminusOne)
    (hc : C.energyShift.im = 0) (hr : IsRealType (CoeffPair.toMax 2 (C.criticalSource q)))
    (energy : ℂ) (hi : energy.im ≠ 0) : energy ∈ C.energyRootDomain q := by
  have ha : (energy+C.energyShift).im ≠ 0 := by simpa only [add_im,hc,add_zero] using hi
  refine ⟨Or.inr ha,?_⟩
  have hz : (sqrt (energy+C.energyShift)).im ≠ 0 := by
    intro hzero
    have he := congrArg Complex.im (sq_sqrt (energy+C.energyShift))
    apply ha
    simpa only [pow_two,mul_im,hzero,mul_zero,zero_mul,add_zero] using he.symm
  intro n hn
  exact hz (sourcePeriodicSegment_im_eq_zero_of_realType (by simp) (by norm_num)
    (C.criticalSource q) hr n _ hn)

theorem exists_common_real_energyRoot_value (C E : HillHminusMiuraChart)
    (q : PeriodOneHminusOne) (hqC : q ∈ C.domain) (hqE : q ∈ E.domain)
    (hc : C.energyShift.im = 0) (he : E.energyShift.im = 0)
    (hrC : IsRealType (CoeffPair.toMax 2 (C.criticalSource q)))
    (hrE : IsRealType (CoeffPair.toMax 2 (E.criticalSource q))) :
    ∃ energy : ℂ, energy.im = 0 ∧ energy ∈ C.energyRootDomain q ∩ E.energyRootDomain q ∧
      C.energyRoot q energy = E.energyRoot q energy := by
  obtain ⟨N,_,hN⟩ := exists_high_shifted_real_band (by simp) (by norm_num) (C.criticalSource q) C.energyShift hc
  obtain ⟨M,_,hM⟩ := exists_high_shifted_real_band (by simp) (by norm_num) (E.criticalSource q) E.energyShift he
  let n := max N M
  let w : ℂ := ((Real.pi*(n:ℝ)+Real.pi/2 : ℝ):ℂ)
  let z := sqrt (w^2+C.energyShift)
  let v := sqrt (w^2+E.energyShift)
  obtain ⟨hz,hzi,hzb⟩ := hN n (le_max_left _ _)
  obtain ⟨hv,hvi,hvb⟩ := hM n (le_max_right _ _)
  have hzreal : (z.re:ℂ) = z := Complex.ext rfl (by simpa only [ofReal_im] using hzi.symm)
  have hvreal : (v.re:ℂ) = v := Complex.ext rfl (by simpa only [ofReal_im] using hvi.symm)
  have hzdom := sourceRealBand_subset_rootDomain (by simp) (by norm_num) (C.criticalSource q) hrC (n:ℤ) z.re hzb
  have hvdom := sourceRealBand_subset_rootDomain (by simp) (by norm_num) (E.criticalSource q) hrE (n:ℤ) v.re hvb
  have hzsq : z^2 = w^2+C.energyShift := sq_sqrt _
  have hvsq : v^2 = w^2+E.energyShift := sq_sqrt _
  have hDC : w^2 ∈ C.energyRootDomain q := by
    refine ⟨?_,?_⟩
    · rw [← hzsq]
      exact square_mem_slitPlane_of_re_pos z hz
    · rw [hzreal] at hzdom
      exact hzdom
  have hDE : w^2 ∈ E.energyRootDomain q := by
    refine ⟨?_,?_⟩
    · rw [← hvsq]
      exact square_mem_slitPlane_of_re_pos v hv
    · rw [hvreal] at hvdom
      exact hvdom
  have hsignC := sourceCanonicalRoot_realBand_sign (by simp) (by norm_num) (C.criticalSource q) hrC (n:ℤ) z.re hzb
  have hsignE := sourceCanonicalRoot_realBand_sign (by simp) (by norm_num) (E.criticalSource q) hrE (n:ℤ) v.re hvb
  rw [hzreal] at hsignC
  rw [hvreal] at hsignE
  change (C.energyRoot q (w^2)).re = 0 ∧ (-1:ℝ)^(n:ℤ).natAbs*(C.energyRoot q (w^2)).im < 0 at hsignC
  change (E.energyRoot q (w^2)).re = 0 ∧ (-1:ℝ)^(n:ℤ).natAbs*(E.energyRoot q (w^2)).im < 0 at hsignE
  have hs : C.energyRoot q (w^2)^2 = E.energyRoot q (w^2)^2 := by
    rw [C.energyRoot_sq q hqC _ hDC,E.energyRoot_sq q hqE _ hDE]
  refine ⟨w^2,by simp [w,pow_two],⟨hDC,hDE⟩,?_⟩
  rcases eq_or_eq_neg_of_sq_eq_sq _ _ hs with h | h
  · exact h
  · rw [h,neg_im,mul_neg] at hsignC
    linarith [hsignC.2,hsignE.2]

theorem energyRoot_eq_on_real_input (C E : HillHminusMiuraChart)
    (q : PeriodOneHminusOne) (hqC : q ∈ C.domain) (hqE : q ∈ E.domain)
    (hc : C.energyShift.im = 0) (he : E.energyShift.im = 0)
    (hrC : IsRealType (CoeffPair.toMax 2 (C.criticalSource q)))
    (hrE : IsRealType (CoeffPair.toMax 2 (E.criticalSource q))) :
    EqOn (C.energyRoot q) (E.energyRoot q) (C.energyRootDomain q ∩ E.energyRootDomain q) := by
  obtain ⟨energy,hreal,henergy,hvalue⟩ := C.exists_common_real_energyRoot_value E q hqC hqE hc he hrC hrE
  obtain ⟨hCo,hCa⟩ := C.energyRoot_spectral_real q hrC
  obtain ⟨hEo,hEa⟩ := E.energyRoot_spectral_real q hrE
  have hopen := hCo.inter hEo
  have hconn := isPreconnected_of_contains_nonreal
    (D := C.energyRootDomain q ∩ E.energyRootDomain q)
    (fun z hz => ⟨C.nonreal_mem_energyRootDomain q hc hrC z hz,
      E.nonreal_mem_energyRootDomain q he hrE z hz⟩) henergy hreal
  have hsq : ∀ᶠ z in 𝓝 energy, C.energyRoot q z ^ 2 = E.energyRoot q z ^ 2 := by
    filter_upwards [hopen.mem_nhds henergy] with z hz
    rw [C.energyRoot_sq q hqC z hz.1,E.energyRoot_sq q hqE z hz.2]
  have hagree := eventuallyEq_of_sq_eq_of_continuousAt (C.energyRoot q) (E.energyRoot q) energy
    (hCa energy henergy.1).continuousAt (hEa energy henergy.2).continuousAt
    hvalue (E.energyRoot_ne_zero q energy henergy.2) hsq
  exact (hCa.mono inter_subset_left).eqOn_of_preconnected_of_eventuallyEq
    (hEa.mono inter_subset_right) hconn henergy hagree

theorem energyRoot_germ_eq_on_real_input (C E : HillHminusMiuraChart)
    {W₀ W Z₀ Z : Set (CoeffPair 2)}
    {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
    {t : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
    (H : SourceTheorem12_1Data (by simp) (by norm_num) W₀ W s)
    (K : SourceTheorem12_1Data (by simp) (by norm_num) Z₀ Z t)
    {V U : Set PeriodOneHminusOne} (hV : IsOpen V) (hU : IsOpen U)
    (hVC : V ⊆ C.domain) (hUE : U ⊆ E.domain)
    (hVW : ∀ q ∈ V, C.criticalSource q ∈ W) (hUZ : ∀ q ∈ U, E.criticalSource q ∈ Z)
    (q0 : PeriodOneHminusOne) (hqV : q0 ∈ V) (hqU : q0 ∈ U)
    (hc : C.energyShift.im = 0) (he : E.energyShift.im = 0)
    (hrC : IsRealType (CoeffPair.toMax 2 (C.criticalSource q0)))
    (hrE : IsRealType (CoeffPair.toMax 2 (E.criticalSource q0)))
    (energy : ℂ) (henergy : energy ∈ C.energyRootDomain q0 ∩ E.energyRootDomain q0) :
    (fun x : ℂ × PeriodOneHminusOne => C.energyRoot x.2 x.1) =ᶠ[𝓝 (energy,q0)]
      (fun x => E.energyRoot x.2 x.1) := by
  obtain ⟨hCo,hCa⟩ := C.energyRoot_joint H hV hVC hVW
  obtain ⟨hEo,hEa⟩ := E.energyRoot_joint K hU hUE hUZ
  have hpoint : (energy,q0) ∈ C.energyRootJointDomain V ∩ E.energyRootJointDomain U :=
    ⟨⟨hqV,henergy.1⟩,hqU,henergy.2⟩
  have hbase := C.energyRoot_eq_on_real_input E q0 (hVC hqV) (hUE hqU) hc he hrC hrE henergy
  have hsq : ∀ᶠ x : ℂ × PeriodOneHminusOne in 𝓝 (energy,q0),
      C.energyRoot x.2 x.1 ^ 2 = E.energyRoot x.2 x.1 ^ 2 := by
    filter_upwards [(hCo.inter hEo).mem_nhds hpoint] with x hx
    rw [C.energyRoot_sq x.2 (hVC hx.1.1) x.1 hx.1.2,
      E.energyRoot_sq x.2 (hUE hx.2.1) x.1 hx.2.2]
  exact eventuallyEq_of_sq_eq_of_continuousAt _ _ (energy,q0)
    (hCa _ hpoint.1).continuousAt (hEa _ hpoint.2).continuousAt hbase
    (E.energyRoot_ne_zero q0 energy henergy.2) hsq

end HillHminusMiuraChart
end NLS.KdV
