import NLS.KdV.HillHminusOneMiuraEnergyPrincipalSeries
import NLS.ComplexAnalysis.EntireCriticalHilbertBasis

/-! # Full entire Hilbert representation of the actual Miura numerator

Actual quadratic critical growth fills the principal series into an
entire Hilbert basis. Analytic uniqueness then gives the representation
at every energy, including critical centers and the shifted central point.
The earlier local weighted critical labels are not identified here.
-/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV
namespace HillHminusMiuraChart

theorem exists_energyCritical_quadratic_growth (C : HillHminusMiuraChart) (q : PeriodOneHminusOne) :
    ∃ N : ℕ, ∀ j : ℕ+, N < (j:ℕ) → Real.pi^2/8*(j:ℝ)^2 ≤ ‖C.energyCritical q j‖ := by
  let b := canonicalCriticalDisplacement (by simp) (by norm_num)
    (periodOnePotential (C.criticalSource q)) (periodOnePotential_mem _)
  obtain ⟨N,hN⟩ := exists_nat_gt (2*‖b‖/Real.pi+8*‖C.energyShift‖/Real.pi^2+1)
  refine ⟨N,?_⟩
  intro j hj
  have hNj : (N:ℝ) < (j:ℝ) := by exact_mod_cast hj
  have hj1 : 1 ≤ (j:ℝ) := by exact_mod_cast j.pos
  have hcoord : ‖b (j:ℤ)‖ ≤ ‖b‖ := lp.norm_apply_le_norm (by norm_num) b (j:ℤ)
  have he : C.frequencyCritical q j-b (j:ℤ) = (Real.pi:ℂ)*(j:ℂ) := by
    simp only [frequencyCritical,b,canonicalCriticalDisplacement_apply,Int.cast_natCast]
    ring
  have ht := norm_sub_le (C.frequencyCritical q j) (b (j:ℤ))
  rw [he,norm_mul,Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le,Complex.norm_natCast] at ht
  have hfreq : Real.pi/2*(j:ℝ) ≤ ‖C.frequencyCritical q j‖ := by
    have hn : 2*‖b‖/Real.pi < (j:ℝ) := by
      have := div_nonneg (by positivity : 0 ≤ 8*‖C.energyShift‖) (sq_nonneg Real.pi)
      linarith
    have hh := (div_lt_iff₀ Real.pi_pos).mp hn
    linarith
  have hshift : ‖C.energyShift‖ ≤ Real.pi^2/8*(j:ℝ)^2 := by
    have hn : 8*‖C.energyShift‖/Real.pi^2 < (j:ℝ) := by
      have := div_nonneg (by positivity : 0 ≤ 2*‖b‖) Real.pi_pos.le
      linarith
    have hh := (div_lt_iff₀ (by positivity : 0 < Real.pi^2)).mp hn
    nlinarith [mul_nonneg (sq_nonneg Real.pi) (show 0 ≤ (j:ℝ)^2-(j:ℝ) by nlinarith)]
  have hsq := mul_self_le_mul_self (by positivity : 0 ≤ Real.pi/2*(j:ℝ)) hfreq
  have hlo := norm_sub_norm_le (C.frequencyCritical q j^2) C.energyShift
  rw [norm_pow] at hlo
  change _ ≤ ‖C.frequencyCritical q j^2-C.energyShift‖
  nlinarith

end HillHminusMiuraChart

def hillHminusCanonicalNumeratorHilbert (C : HillHminusMiuraChart) (q : PeriodOneHminusOne)
    (energy : ℂ) : Coeff 2 :=
  entireCriticalNumeratorHilbert (deriv (hillHminusDiscriminant q)) (C.energyCritical q) energy

theorem hillHminusCanonicalNumeratorHilbert_spec (C : HillHminusMiuraChart) (q : PeriodOneHminusOne)
    (hq : q ∈ C.domain) (hr : IsRealType (CoeffPair.toMax 2 (C.criticalSource q))) :
    (∀ energy k, hillHminusCanonicalNumeratorHilbert C q energy k =
      entireCriticalNumeratorCoordinates (deriv (hillHminusDiscriminant q)) (C.energyCritical q) energy k) ∧
      AnalyticOnNhd ℂ (hillHminusCanonicalNumeratorHilbert C q) univ := by
  obtain ⟨N,hN⟩ := C.exists_energyCritical_quadratic_growth q
  have hg : AnalyticOnNhd ℂ (deriv (hillHminusDiscriminant q)) univ := by
    intro z _
    exact (analyticOnNhd_hillHminusDiscriminantDerivative (z,q) (mem_univ _)).comp
      (f := fun z : ℂ => (z,q)) (analyticAt_id.prod analyticAt_const)
  exact entireCriticalNumeratorHilbert_spec _ _ hg (C.energyCritical_is_critical q hr hq)
    (Real.pi^2/8) (by positivity) N hN

theorem hillHminusCanonicalNumeratorHilbert_positive (C : HillHminusMiuraChart) (q : PeriodOneHminusOne)
    (hq : q ∈ C.domain) (hr : IsRealType (CoeffPair.toMax 2 (C.criticalSource q)))
    (energy : ℂ) (j : ℕ+) : hillHminusCanonicalNumeratorHilbert C q energy (j:ℤ) =
      entireCriticalNumerator (deriv (hillHminusDiscriminant q)) (C.energyCritical q) j energy := by
  rw [(hillHminusCanonicalNumeratorHilbert_spec C q hq hr).1]
  have hj : (0:ℤ) < j := by exact_mod_cast j.pos
  have hidx : (⟨(j:ℤ).toNat,by omega⟩ : ℕ+) = j := Subtype.ext (Int.toNat_natCast (j:ℕ))
  simp only [entireCriticalNumeratorCoordinates,dif_pos hj,hidx]

theorem hillHminusMiuraEnergyPsi_eq_canonicalHilbert (C : HillHminusMiuraChart)
    (s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n) (n : ℤ) (q : PeriodOneHminusOne)
    (hq : q ∈ C.domain) (hr : IsRealType (CoeffPair.toMax 2 (C.criticalSource q))) (energy : ℂ) :
    hillHminusMiuraEnergyPsi C s n (energy,q) =
      Coeff.dualPairing (hillHminusMiuraEnergyResidueHilbert C s n q hr)
        (hillHminusCanonicalNumeratorHilbert C q energy) := by
  let a := hillHminusMiuraEnergyResidueHilbert C s n q hr
  let B := hillHminusCanonicalNumeratorHilbert C q
  let g := deriv (hillHminusDiscriminant q)
  let P : ℂ → ℂ := fun z => hillHminusMiuraEnergyPsi C s n (z,q)
  let R : ℂ → ℂ := fun z => Coeff.dualPairing a (B z)
  have hB := (hillHminusCanonicalNumeratorHilbert_spec C q hq hr).2
  have hR : AnalyticOnNhd ℂ R univ := by
    intro z _
    exact ((Coeff.dualPairing a).analyticAt (B z)).comp (hB z (mem_univ _))
  have hP := analyticOnNhd_hillHminusMiuraEnergyPsi_spectral C s n q
  have hg : AnalyticOnNhd ℂ g univ := by
    intro z _
    exact (analyticOnNhd_hillHminusDiscriminantDerivative (z,q) (mem_univ _)).comp
      (f := fun z : ℂ => (z,q)) (analyticAt_id.prod analyticAt_const)
  let U := {z : ℂ | z ≠ -C.energyShift ∧ g z ≠ 0}
  have hU : IsOpen U := (isOpen_ne_fun continuous_id continuous_const).inter
    (isOpen_ne_fun hg.continuous continuous_const)
  have heq : EqOn R P U := by
    intro z hz
    obtain ⟨_,hseries⟩ := hillHminusMiura_energy_principal_series C s n q hq hr z hz.1 hz.2
    have ht (j : ℕ+) : a (j:ℤ)*B z (j:ℤ) =
        g z*(hillHminusMiuraEnergyCriticalResidue C s n q j/(z-C.energyCritical q j)) := by
      rw [hillHminusMiuraEnergyResidueHilbert_apply_pos C s n q hq hr j,
        hillHminusCanonicalNumeratorHilbert_positive C q hq hr z j]
      have hne : z-C.energyCritical q j ≠ 0 := sub_ne_zero.mpr (by
        intro h
        exact hz.2 (h ▸ C.energyCritical_is_critical q hr hq j))
      have hf := entireCriticalNumerator_factor g (C.energyCritical q) (C.energyCritical_is_critical q hr hq) j z
      have hb : entireCriticalNumerator g (C.energyCritical q) j z =
          (2*(j:ℂ)*Real.pi)*g z/(z-C.energyCritical q j) :=
        (eq_div_iff hne).mpr ((mul_comm _ _).trans hf)
      rw [hb]
      field_simp
    let f : ℤ → ℂ := fun k => a k*B z k
    have hsum : Summable f := (Coeff.summable_norm_dualPairing a (B z)).of_norm
    have hzero : f 0 = 0 := by
      change hillHminusMiuraEnergyResidueHilbert C s n q hr 0 * _ = 0
      rw [hillHminusMiuraEnergyResidueHilbert_apply_nonpos C s n q hr 0 le_rfl,zero_mul]
    have hneg : ∀ j : ℕ+, f (-(j:ℤ)) = 0 := by
      intro j
      change hillHminusMiuraEnergyResidueHilbert C s n q hr (-(j:ℤ))*_ = 0
      rw [hillHminusMiuraEnergyResidueHilbert_apply_nonpos C s n q hr _ (by omega),zero_mul]
    have hsplit := tsum_int_eq_zero_add_tsum_pnat (f := f) hsum
    simp only [hzero,hneg,tsum_zero,zero_add,add_zero] at hsplit
    calc
      R z = ∑' j : ℕ+, a (j:ℤ)*B z (j:ℤ) := hsplit
      _ = ∑' j : ℕ+, g z*(hillHminusMiuraEnergyCriticalResidue C s n q j/(z-C.energyCritical q j)) := tsum_congr ht
      _ = g z*(∑' j : ℕ+, hillHminusMiuraEnergyCriticalResidue C s n q j/(z-C.energyCritical q j)) := tsum_mul_left
      _ = g z*(P z/g z) := by rw [hseries]
      _ = P z := by field_simp [hz.2]
  let z0 := I-C.energyShift
  have hz0 : z0 ∈ U := by
    constructor
    · intro h
      have hi := congrArg Complex.im h
      change 1-C.energyShift.im = -C.energyShift.im at hi
      linarith
    · intro h
      obtain ⟨j,hj⟩ := (C.energyCritical_exhaustive q hr hq z0).mp h
      have hi := congrArg Complex.im hj
      have hb := (C.frequencyCritical_pos_real q hr j).2
      simp only [HillHminusMiuraChart.energyCritical,sub_im,pow_two,mul_im,hb,mul_zero,zero_mul,add_zero] at hi
      change 0-C.energyShift.im = 1-C.energyShift.im at hi
      linarith
  have hagree : R =ᶠ[𝓝 z0] P := by filter_upwards [hU.mem_nhds hz0] with z hz; exact heq hz
  exact ((hR.eqOn_of_preconnected_of_eventuallyEq hP isPreconnected_univ (mem_univ z0) hagree)
    (mem_univ energy)).symm

/-- One actual normalized data set and one complex rough-open neighborhood
precede every real input, numerator index and energy. The entire Hilbert
representation retains its exact critical-basis coefficients. -/
theorem exists_hillHminus_real_canonical_numerator_representation (q0 : PeriodOneHminusOne)
    (hq0 : periodOneHminusConjugation q0 = q0) :
    ∃ C : HillHminusMiuraChart, ∃ V : Set PeriodOneHminusOne,
      ∃ W₀ W : Set (CoeffPair 2), ∃ s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n,
        IsOpen V ∧ q0 ∈ V ∧ V ⊆ C.domain ∧
        SourceTheorem12_1Data (by simp) (by norm_num) W₀ W s ∧
        (∀ q ∈ V, C.criticalSource q ∈ W) ∧
        (∀ n : ℤ, AnalyticOnNhd ℂ (hillHminusMiuraEnergyPsi C s n) (univ ×ˢ V)) ∧
        ∀ q ∈ V, periodOneHminusConjugation q = q → ∀ n : ℤ,
          ∃ a : Coeff 2, (∀ k : ℤ, k ≤ 0 → a k = 0) ∧
            (∀ j : ℕ+, a (j:ℤ) = hillHminusMiuraEnergyCriticalResidue C s n q j /
              (2*(j:ℂ)*Real.pi)) ∧
            ∀ energy : ℂ, hillHminusMiuraEnergyPsi C s n (energy,q) =
              Coeff.dualPairing a (hillHminusCanonicalNumeratorHilbert C q energy) := by
  obtain ⟨C,V,W₀,W,s,hV,hqV,hVC,_,_,_,hr,H,hVW,hP,_,_⟩ :=
    exists_hillHminus_real_normalized_energy_pullbacks q0 hq0
  refine ⟨C,V,W₀,W,s,hV,hqV,hVC,H,hVW,hP,?_⟩
  intro q hq hreal n
  have hsource := (hr q (hVC hq) hreal).2
  exact ⟨hillHminusMiuraEnergyResidueHilbert C s n q hsource,
    hillHminusMiuraEnergyResidueHilbert_apply_nonpos C s n q hsource,
    hillHminusMiuraEnergyResidueHilbert_apply_pos C s n q (hVC hq) hsource,
    hillHminusMiuraEnergyPsi_eq_canonicalHilbert C s n q (hVC hq) hsource⟩

end NLS.KdV
