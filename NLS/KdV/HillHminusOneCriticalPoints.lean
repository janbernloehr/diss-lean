import NLS.KdV.HillHminusOneSourcePrimitive
import NLS.KdV.HillFreeEnergyShift
import NLS.KdV.ClassicalHighCriticalPoints

/-! # Actual analytic high critical energies on complex Hminus1 neighborhoods

A fixed actual Miura chart transfers the complex canonical ZS critical
family through the shifted square coordinate. The resulting points are
critical energies of the independently glued rough Hill trace.
-/
noncomputable section
open Set Metric Complex Filter Topology NLS.ZakharovShabat NLS.ComplexAnalysis
namespace NLS.KdV

def hillHminusDiscriminantDerivative (t : ℂ × PeriodOneHminusOne) : ℂ :=
  deriv (hillHminusDiscriminant t.2) t.1

theorem analyticOnNhd_hillHminusDiscriminantDerivative :
    AnalyticOnNhd ℂ hillHminusDiscriminantDerivative univ :=
  analyticOnNhd_spectral_deriv_of_analyticOnNhd _ univ isOpen_univ
    analyticOnNhd_hillHminusDiscriminant_joint

theorem analyticOnNhd_hillHminusDiscriminantSecondDerivative :
    AnalyticOnNhd ℂ (fun t : ℂ × PeriodOneHminusOne =>
      deriv (deriv (hillHminusDiscriminant t.2)) t.1) univ :=
  analyticOnNhd_spectral_deriv_of_analyticOnNhd _ univ isOpen_univ
    analyticOnNhd_hillHminusDiscriminantDerivative

namespace HillHminusMiuraChart

def criticalSource (C : HillHminusMiuraChart) (q : PeriodOneHminusOne) : CoeffPair 2 :=
  hillMiuraDiagonal (C.lift q)

def frequencyCritical (C : HillHminusMiuraChart) (q : PeriodOneHminusOne) (n : ℕ+) : ℂ :=
  canonicalCriticalPoints (by simp) (by norm_num) (periodOnePotential (C.criticalSource q))
    (periodOnePotential_mem _) (n : ℤ)

def energyCritical (C : HillHminusMiuraChart) (q : PeriodOneHminusOne) (n : ℕ+) : ℂ :=
  C.frequencyCritical q n^2-C.energyShift

theorem analyticOnNhd_criticalSource (C : HillHminusMiuraChart) :
    AnalyticOnNhd ℂ C.criticalSource C.domain := by
  intro q hq
  exact (hillMiuraDiagonal.analyticAt _).comp (C.lift_analytic q hq)

theorem trace_shifted_square (C : HillHminusMiuraChart)
    (q : PeriodOneHminusOne) (hq : q ∈ C.domain) (z : ℂ) :
    hillHminusDiscriminant q (z^2-C.energyShift) =
      canonicalDiscriminant (by simp) (periodOnePotential (C.criticalSource q)) z := by
  rw [hillHminusDiscriminant_eq_chart C q hq]
  change hillMiuraL2Discriminant (C.lift q) (z^2-C.energyShift+C.energyShift) = _
  rw [sub_add_cancel,hillMiuraL2Discriminant]
  rcases eq_or_eq_neg_of_sq_eq_sq (sqrt (z^2)) z (complex_sqrt_sq _) with he | he
  · rw [he]
    rfl
  · rw [he,hillMiuraFrequencyTrace_even]
    rfl

theorem frequency_derivative_eq (C : HillHminusMiuraChart)
    (q : PeriodOneHminusOne) (hq : q ∈ C.domain) (z : ℂ) :
    deriv (canonicalDiscriminant (by simp) (periodOnePotential (C.criticalSource q))) z =
      (2*z)*deriv (hillHminusDiscriminant q) (z^2-C.energyShift) := by
  have he : canonicalDiscriminant (by simp) (periodOnePotential (C.criticalSource q)) =
      (fun w : ℂ => hillHminusDiscriminant q (w^2-C.energyShift)) :=
    funext (fun w => (C.trace_shifted_square q hq w).symm)
  rw [he]
  have hsq : HasDerivAt (fun w : ℂ => w^2-C.energyShift) (2*z) z := by
    simpa using! ((hasDerivAt_id z).pow 2).sub_const C.energyShift
  have hD : AnalyticAt ℂ (hillHminusDiscriminant q) (z^2-C.energyShift) :=
    (analyticOnNhd_hillHminusDiscriminant_joint _ (mem_univ _)).comp
      (f := fun w : ℂ => (w,q)) (analyticAt_id.prod analyticAt_const)
  have hd := hD.differentiableAt.hasDerivAt.comp z hsq
  change HasDerivAt (fun w : ℂ => hillHminusDiscriminant q (w^2-C.energyShift))
    (deriv (hillHminusDiscriminant q) (z^2-C.energyShift)*(2*z)) z at hd
  exact hd.deriv.trans (by ring)

theorem frequency_second_derivative_eq (C : HillHminusMiuraChart)
    (q : PeriodOneHminusOne) (hq : q ∈ C.domain) (z : ℂ) :
    deriv (deriv (canonicalDiscriminant (by simp) (periodOnePotential (C.criticalSource q)))) z =
      2*deriv (hillHminusDiscriminant q) (z^2-C.energyShift)+
        4*z^2*deriv (deriv (hillHminusDiscriminant q)) (z^2-C.energyShift) := by
  have he : deriv (canonicalDiscriminant (by simp) (periodOnePotential (C.criticalSource q))) =
      (fun w : ℂ => (2*w)*deriv (hillHminusDiscriminant q) (w^2-C.energyShift)) :=
    funext (C.frequency_derivative_eq q hq)
  rw [he]
  have hsq : HasDerivAt (fun w : ℂ => w^2-C.energyShift) (2*z) z := by
    simpa using! ((hasDerivAt_id z).pow 2).sub_const C.energyShift
  have hD : AnalyticAt ℂ (hillHminusDiscriminant q) (z^2-C.energyShift) :=
    (analyticOnNhd_hillHminusDiscriminant_joint _ (mem_univ _)).comp
      (f := fun w : ℂ => (w,q)) (analyticAt_id.prod analyticAt_const)
  have hd := hD.deriv.differentiableAt.hasDerivAt.comp z hsq
  have htwo : HasDerivAt (fun w : ℂ => (2 : ℂ)*w) 2 z := by
    simpa using! (hasDerivAt_id z).const_mul 2
  have hp := htwo.mul hd
  change HasDerivAt (fun w : ℂ => (2*w)*deriv (hillHminusDiscriminant q) (w^2-C.energyShift))
    (2*deriv (hillHminusDiscriminant q) (z^2-C.energyShift)+
      (2*z)*(deriv (deriv (hillHminusDiscriminant q)) (z^2-C.energyShift)*(2*z))) z at hp
  exact hp.deriv.trans (by ring)

end HillHminusMiuraChart

/-- One genuine Hminus1-open neighborhood precedes the entire analytic
simple high critical family, with unique labels on the shifted discs. -/
theorem exists_analytic_hillHminus_high_critical_points (q0 : PeriodOneHminusOne) :
    ∃ C : HillHminusMiuraChart, ∃ N : ℕ, ∃ V : Set PeriodOneHminusOne,
      0 < N ∧ IsOpen V ∧ q0 ∈ V ∧ V ⊆ C.domain ∧
      ∀ n : ℕ+, N < (n : ℕ) →
        AnalyticOnNhd ℂ (fun q => C.frequencyCritical q n) V ∧
        AnalyticOnNhd ℂ (fun q => C.energyCritical q n) V ∧
        ∀ q ∈ V,
          C.frequencyCritical q n ∈ ball ((Real.pi : ℂ)*(n : ℕ)) (Real.pi/4) ∧
          deriv (hillHminusDiscriminant q) (C.energyCritical q n) = 0 ∧
          deriv (deriv (hillHminusDiscriminant q)) (C.energyCritical q n) ≠ 0 ∧
          ∀ lambda ∈ (fun z : ℂ => z^2-C.energyShift) ''
            closedBall ((Real.pi : ℂ)*(n : ℕ)) (Real.pi/4),
            deriv (hillHminusDiscriminant q) lambda = 0 ↔ lambda = C.energyCritical q n := by
  obtain ⟨C,hqC⟩ := exists_hillHminusMiuraChart q0
  let phi : PeriodOneHminusOne → PairSpace 2 := fun q => periodOnePotential (C.criticalSource q)
  have hphi : AnalyticOnNhd ℂ phi C.domain := by
    intro q hq
    exact ((periodOnePotential (p := 2)).analyticAt _).comp (C.analyticOnNhd_criticalSource q hq)
  obtain ⟨Na,Ua,hNa,hUa,hqa,ha⟩ := exists_local_source_distantCanonicalCriticalPoints_analytic_complex
    (by simp) (by norm_num) (C.criticalSource q0)
  obtain ⟨Nl,hNl,Ul,hUl,_,hql,_,R,hR,hlabel⟩ :=
    exists_uniform_canonicalCriticalPoints (by simp) (by norm_num) (phi q0)
  let V := (C.domain ∩ C.criticalSource ⁻¹' Ua) ∩ (C.domain ∩ phi ⁻¹' Ul)
  have hV : IsOpen V := (C.analyticOnNhd_criticalSource.continuousOn.isOpen_inter_preimage C.domain_open hUa).inter
    (hphi.continuousOn.isOpen_inter_preimage C.domain_open hUl)
  refine ⟨C,max Na Nl,V,hNa.trans_le (le_max_left _ _),hV,⟨⟨hqC,hqa⟩,hqC,hql⟩,
    fun _ hq => hq.1.1,?_⟩
  intro n hn
  have hna : Na < (n : ℤ).natAbs := by simpa using (le_max_left Na Nl).trans_lt hn
  have hnl : Nl < (n : ℤ).natAbs := by simpa using (le_max_right Na Nl).trans_lt hn
  have han : AnalyticOnNhd ℂ (fun q => C.frequencyCritical q n) V := by
    intro q hq
    exact (ha _ hq.1.2 (n : ℤ) hna).1.comp (C.analyticOnNhd_criticalSource q hq.1.1)
  refine ⟨han,fun q hq => ((han q hq).pow 2).sub analyticAt_const,?_⟩
  intro q hq
  have hl := ((hlabel _ hq.2.2 (periodOnePotential_mem _)).1.distant (n : ℤ) hnl)
  have hmem : C.frequencyCritical q n ∈ ball ((Real.pi : ℂ)*(n : ℕ)) (Real.pi/4) := by
    simpa only [HillHminusMiuraChart.frequencyCritical,phi,Int.cast_natCast] using! hl.1
  have hz0 : C.frequencyCritical q n ≠ 0 := by
    intro he
    have hh := re_pos_of_high_closedBall (n : ℕ) n.property _ (ball_subset_closedBall hmem)
    simp only [he,zero_re,lt_self_iff_false] at hh
  have hcrit : deriv (hillHminusDiscriminant q) (C.energyCritical q n) = 0 := by
    have he := C.frequency_derivative_eq q hq.1.1 (C.frequencyCritical q n)
    have hc : deriv (canonicalDiscriminant (by simp) (phi q)) (C.frequencyCritical q n) = 0 := hl.2.1
    rw [hc] at he
    exact (mul_eq_zero.mp he.symm).resolve_left (mul_ne_zero (by norm_num) hz0)
  have hsimple : deriv (deriv (hillHminusDiscriminant q)) (C.energyCritical q n) ≠ 0 := by
    have hs := (ha _ hq.1.2 (n : ℤ) hna).2
    intro he
    apply hs
    rw [C.frequency_second_derivative_eq q hq.1.1]
    change 2*deriv (hillHminusDiscriminant q) (C.energyCritical q n)+
      4*(C.frequencyCritical q n)^2*deriv (deriv (hillHminusDiscriminant q)) (C.energyCritical q n) = 0
    rw [hcrit,he]
    ring
  refine ⟨hmem,hcrit,hsimple,?_⟩
  rintro lambda ⟨z,hz,rfl⟩
  constructor
  · intro he
    have hc : deriv (canonicalDiscriminant (by simp) (phi q)) z = 0 := by
      rw [C.frequency_derivative_eq q hq.1.1,he,mul_zero]
    have heq := (hl.2.2.2 z (by simpa only [Int.cast_natCast] using hz)).mp hc
    exact congrArg (fun w : ℂ => w^2-C.energyShift) heq
  · intro he
    exact he ▸ hcrit

/-- The high rough critical family has the exact unshifted free energy
labels, even though its auxiliary Miura chart uses an energy shift. -/
theorem exists_hillHminus_high_critical_points_free :
    ∃ C : HillHminusMiuraChart, ∃ N : ℕ, ∃ V : Set PeriodOneHminusOne,
      0 < N ∧ IsOpen V ∧ 0 ∈ V ∧ V ⊆ C.domain ∧
      ∀ n : ℕ+, N < (n : ℕ) →
        C.energyCritical 0 n = freeHillEnergy n ∧
        AnalyticOnNhd ℂ (fun q => C.energyCritical q n) V ∧
        ∀ q ∈ V, deriv (hillHminusDiscriminant q) (C.energyCritical q n) = 0 ∧
          deriv (deriv (hillHminusDiscriminant q)) (C.energyCritical q n) ≠ 0 := by
  obtain ⟨C,N,V,hN,hV,h0V,hVC,hdata⟩ := exists_analytic_hillHminus_high_critical_points 0
  obtain ⟨Ns,_,hshift⟩ := exists_high_disc_sqrt_shift_small C.energyShift (Real.pi/4) (Real.pi/4) (by positivity)
  refine ⟨C,max N Ns,V,hN.trans_le (le_max_left _ _),hV,h0V,hVC,?_⟩
  intro n hn
  have hnn : N < (n : ℕ) := (le_max_left _ _).trans_lt hn
  have hns : Ns ≤ (n : ℕ) := (le_max_right _ _).trans hn.le
  obtain ⟨_,han,hcrit⟩ := hdata n hnn
  refine ⟨?_,han,fun q hq => ⟨(hcrit q hq).2.1,(hcrit q hq).2.2.1⟩⟩
  let z : ℂ := sqrt (((Real.pi : ℂ)*(n : ℕ))^2+C.energyShift)
  have hz : z ∈ closedBall ((Real.pi : ℂ)*(n : ℕ)) (Real.pi/4) :=
    ball_subset_closedBall (mem_ball_iff_norm.mpr ((hshift (n : ℕ) hns _ (mem_closedBall_self (by positivity))).2))
  have he : z^2-C.energyShift = freeHillEnergy n := by
    dsimp only [z]
    rw [complex_sqrt_sq]
    dsimp only [freeHillEnergy]
    push_cast
    ring
  have hf : hillHminusDiscriminant 0 = classicalHillDiscriminant 0 := by
    funext lambda
    rw [hillHminusDiscriminant_zero,classicalHillDiscriminant_zero]
  have hc : deriv (hillHminusDiscriminant 0) (freeHillEnergy n) = 0 := by
    rw [hf]
    exact deriv_classicalHillDiscriminant_free_energy n
  exact ((hcrit 0 h0V).2.2.2 (freeHillEnergy n) ⟨z,hz,he⟩).mp hc |>.symm

end NLS.KdV
