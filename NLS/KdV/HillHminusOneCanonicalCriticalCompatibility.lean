import NLS.KdV.FreeHillCriticalEnergies
import NLS.KdV.HillHminusOneCriticalChartGerms
import NLS.KdV.CanonicalMiuraNumeratorRepresentation
import NLS.KdV.HillHminusOneNumeratorHilbert
import NLS.SequenceSpaces.PeriodOneRealScaling

/-! # Actual canonical and earlier period-data critical bases agree

Complete free labels and analytic uniqueness on real radial path images
identify the earlier critical branches and their full complex germs. Filled
bases then agree at every energy. The actual descended numerator belongs
to the earlier Hilbert class. Actual contour normalization and agreement
with the weighted normalized family still require proof.
-/
noncomputable section
open Set Metric Filter Topology Complex NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV

/-- Every canonical positive energy label has its exact free value. -/
theorem hillHminusMiura_energyCritical_free (C : HillHminusMiuraChart) (hq : 0 ∈ C.domain)
    (hr : IsRealType (CoeffPair.toMax 2 (C.criticalSource 0)))
    (hc : C.energyShift.im = 0) (j : ℕ+) : C.energyCritical 0 j = freeHillEnergy j := by
  have htrace : hillHminusDiscriminant 0 = classicalHillDiscriminant 0 := by
    funext z
    rw [hillHminusDiscriminant_zero,classicalHillDiscriminant_zero]
  have hfreeMono : StrictMono (fun n : ℕ+ => (freeHillEnergy n).re) := by
    intro n m hnm
    have hn : (0 : ℝ) < n := by exact_mod_cast n.pos
    have hnmR : (n : ℝ) < m := by exact_mod_cast hnm
    simp only [freeHillEnergy,ofReal_re]
    have hmul := mul_lt_mul_of_pos_right hnmR Real.pi_pos
    have hpos := mul_pos hn Real.pi_pos
    nlinarith
  have heq : range (fun n : ℕ+ => (C.energyCritical 0 n).re) =
      range (fun n : ℕ+ => (freeHillEnergy n).re) := by
    ext x
    constructor
    · rintro ⟨n,rfl⟩
      have hz := C.energyCritical_is_critical 0 hr hq n
      rw [htrace] at hz
      obtain ⟨m,hm⟩ := (classicalHill_free_critical_exhaustive _).mp hz
      exact ⟨m,congrArg Complex.re hm⟩
    · rintro ⟨n,rfl⟩
      have hz : deriv (hillHminusDiscriminant 0) (freeHillEnergy n) = 0 := by
        rw [htrace]
        exact deriv_classicalHillDiscriminant_free_energy n
      obtain ⟨m,hm⟩ := (C.energyCritical_exhaustive 0 hr hq _).mp hz
      exact ⟨m,congrArg Complex.re hm⟩
  have h := (C.strictMono_energyCritical_re 0 hr).range_inj hfreeMono |>.mp heq
  apply Complex.ext
  · exact congrFun h j
  · rw [C.energyCritical_im_eq_zero 0 hr hc j]
    simp only [freeHillEnergy,ofReal_im]

/-- An analytic actual critical branch with the correct free value agrees with the canonical branch along any real radial path, including its full complex germ at the endpoint. -/
theorem hillHminus_critical_branch_eq_canonical_of_real_path (C : HillHminusMiuraChart)
    {V : Set PeriodOneHminusOne} (hV : IsOpen V) (h0V : (0 : PeriodOneHminusOne) ∈ V)
    (hVC : V ⊆ C.domain) (hc : C.energyShift.im = 0)
    (hr : ∀ p ∈ V, periodOneHminusConjugation p = p →
      IsRealType (CoeffPair.toMax 2 (C.criticalSource p)))
    (j : ℕ+) (b : PeriodOneHminusOne → ℂ) (hb : AnalyticOnNhd ℂ b V)
    (hb0 : b 0 = freeHillEnergy j)
    (hz : ∀ p ∈ V, deriv (hillHminusDiscriminant p) (b p) = 0)
    (q : PeriodOneHminusOne) (hq : periodOneHminusConjugation q = q)
    (hpath : ∀ r ∈ Icc (0 : ℝ) 1, (r : ℂ) • q ∈ V) :
    b q = C.energyCritical q j ∧ b =ᶠ[𝓝 q] (fun p => C.energyCritical p j) := by
  let p : ℝ → PeriodOneHminusOne := fun r => (r : ℂ) • q
  let K := p '' Icc (0 : ℝ) 1
  have hpc : Continuous p := by dsimp only [p]; fun_prop
  have hKV : K ⊆ V := by
    rintro x ⟨r,hrange,rfl⟩
    exact hpath r hrange
  have hKr : ∀ x ∈ K, periodOneHminusConjugation x = x := by
    rintro x ⟨r,_,rfl⟩
    exact periodOneHminusConjugation_real_smul_fixed r q hq
  have h0K : (0 : PeriodOneHminusOne) ∈ K := by
    refine ⟨0,⟨le_rfl,by norm_num⟩,?_⟩
    simp [p]
  have hqK : q ∈ K := by
    refine ⟨1,⟨by norm_num,le_rfl⟩,?_⟩
    simp [p]
  have h0source := hr 0 h0V periodOneHminusConjugation_zero
  have hinit : b =ᶠ[𝓝 0] (fun p => C.energyCritical p j) := by
    apply C.eventuallyEq_energyCritical_of_simple_root 0 (hVC h0V) h0source j b
      (hb 0 h0V).continuousAt
    · rw [hb0,hillHminusMiura_energyCritical_free C (hVC h0V) h0source hc j]
    · filter_upwards [hV.mem_nhds h0V] with x hx
      exact hz x hx
  have han : AnalyticOnNhd ℂ (fun p => C.energyCritical p j) K := by
    intro x hx
    exact C.analyticAt_energyCritical_of_realType x (hr x (hKV hx) (hKr x hx)) (hVC (hKV hx)) j
  have hvalue := (hb.mono hKV).eqOn_of_preconnected_of_eventuallyEq han
    (isPreconnected_Icc.image p hpc.continuousOn) h0K hinit hqK
  refine ⟨hvalue,?_⟩
  apply C.eventuallyEq_energyCritical_of_simple_root q (hVC (hKV hqK))
    (hr q (hKV hqK) hq) j b (hb q (hKV hqK)).continuousAt hvalue
  filter_upwards [hV.mem_nhds (hKV hqK)] with x hx
  exact hz x hx

/-- Matching critical labels identify the filled scalar bases at every energy. -/
theorem hillHminusUniformNumerator_eq_canonical (C D : HillHminusMiuraChart) (N : ℕ)
    {V : Set PeriodOneHminusOne}
    (j : ℕ+) (hb : AnalyticOnNhd ℂ (hillHminusUniformCriticalPoint D N j) V)
    (q : PeriodOneHminusOne) (hq : q ∈ V)
    (he : hillHminusUniformCriticalPoint D N j q = C.energyCritical q j) (energy : ℂ) :
    hillHminusUniformNumerator D N j (energy,q) =
      entireCriticalNumerator (deriv (hillHminusDiscriminant q)) (C.energyCritical q) j energy := by
  unfold hillHminusUniformNumerator
  rw [parametricMovingDividedDifference_eq_dslope hillHminusDiscriminantDerivative
    (hillHminusUniformCriticalPoint D N j)
    (analyticOnNhd_hillHminusDiscriminantDerivative.mono (subset_univ _)) hb energy q hq]
  change (2*(j:ℂ)*Real.pi)*dslope (deriv (hillHminusDiscriminant q))
    (hillHminusUniformCriticalPoint D N j q) energy = _
  rw [he]
  rfl

/-- Matching all critical labels identifies the entire Hilbert bases. -/
theorem hillHminusNumeratorHilbert_eq_canonical (C D : HillHminusMiuraChart) (N : ℕ)
    {V : Set PeriodOneHminusOne}
    (hb : ∀ j, AnalyticOnNhd ℂ (hillHminusUniformCriticalPoint D N j) V)
    (q : PeriodOneHminusOne) (hq : q ∈ V)
    (he : ∀ j, hillHminusUniformCriticalPoint D N j q = C.energyCritical q j) (energy : ℂ) :
    hillHminusNumeratorHilbert D N (energy,q) = hillHminusCanonicalNumeratorHilbert C q energy := by
  unfold hillHminusNumeratorHilbert hillHminusCanonicalNumeratorHilbert entireCriticalNumeratorHilbert
  apply congrArg (Coeff.ofFunctionOrZero 2)
  funext k
  by_cases hk : 0 < k
  · simp only [hillHminusNumeratorCoordinates,entireCriticalNumeratorCoordinates,dif_pos hk]
    exact hillHminusUniformNumerator_eq_canonical C D N _ (hb _) q hq (he _) energy
  · simp only [hillHminusNumeratorCoordinates,entireCriticalNumeratorCoordinates,dif_neg hk]

/-- One norm ball precedes all real inputs, positive labels and energies in the compatibility of the actual earlier period data with a real canonical chart. -/
theorem hillHminus_period_data_canonical_compatibility
    (C D : HillHminusMiuraChart) {N : ℕ} {V : Set PeriodOneHminusOne}
    (E : HillHminusAllContourPeriodData D N V) (h0C : 0 ∈ C.domain)
    (hc : C.energyShift.im = 0)
    (hr : ∀ q ∈ C.domain, periodOneHminusConjugation q = q →
      IsRealType (CoeffPair.toMax 2 (C.criticalSource q))) :
    ∃ δ : ℝ, 0 < δ ∧ ball (0 : PeriodOneHminusOne) δ ⊆ V ∧
      ball (0 : PeriodOneHminusOne) δ ⊆ C.domain ∧
      ∀ q ∈ ball (0 : PeriodOneHminusOne) δ, periodOneHminusConjugation q = q →
        (∀ j : ℕ+, hillHminusUniformCriticalPoint D N j q = C.energyCritical q j ∧
          hillHminusUniformCriticalPoint D N j =ᶠ[𝓝 q] (fun p => C.energyCritical p j)) ∧
        ∀ energy : ℂ, hillHminusNumeratorHilbert D N (energy,q) =
          hillHminusCanonicalNumeratorHilbert C q energy := by
  let W := V ∩ C.domain
  have hW : IsOpen W := E.isOpen.inter C.domain_open
  have h0W : (0 : PeriodOneHminusOne) ∈ W := ⟨E.zero_mem,h0C⟩
  obtain ⟨δ,hδ,hball⟩ := Metric.isOpen_iff.mp hW 0 h0W
  refine ⟨δ,hδ,fun q hq => (hball hq).1,fun q hq => (hball hq).2,?_⟩
  intro q hq hreal
  have hpath (r : ℝ) (hrange : r ∈ Icc (0 : ℝ) 1) : (r : ℂ) • q ∈ W := by
    apply hball
    rw [mem_ball_zero_iff,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hrange.1]
    exact (mul_le_of_le_one_left (norm_nonneg q) hrange.2).trans_lt (mem_ball_zero_iff.mp hq)
  have hlabels (j : ℕ+) := hillHminus_critical_branch_eq_canonical_of_real_path C hW h0W inter_subset_right hc
    (fun p hp hpr => hr p hp.2 hpr) j _
    ((E.critical_analytic j).mono inter_subset_left) (E.critical_free j)
    (fun p hp => E.critical_zero j p hp.1) q hreal hpath
  exact ⟨hlabels,fun energy => hillHminusNumeratorHilbert_eq_canonical C D N E.critical_analytic
    q (hball hq).1 (fun j => (hlabels j).1) energy⟩

/-- The actual descended Miura numerator is represented in the earlier period-data Hilbert basis with genuine residue coefficients, on one common norm ball. -/
theorem hillHminus_period_data_actual_numerator_representation
    (C D : HillHminusMiuraChart) {N : ℕ} {V : Set PeriodOneHminusOne}
    (E : HillHminusAllContourPeriodData D N V) (h0C : 0 ∈ C.domain)
    (hc : C.energyShift.im = 0)
    (hr : ∀ q ∈ C.domain, periodOneHminusConjugation q = q →
      IsRealType (CoeffPair.toMax 2 (C.criticalSource q))) :
    ∃ δ : ℝ, 0 < δ ∧ ball (0 : PeriodOneHminusOne) δ ⊆ V ∧
      ∀ q ∈ ball (0 : PeriodOneHminusOne) δ, ∃ hqC : q ∈ C.domain,
        ∀ hreal : periodOneHminusConjugation q = q,
          ∀ s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n, ∀ n : ℤ, ∀ energy : ℂ,
            hillHminusMiuraEnergyPsi C s n (energy,q) =
              Coeff.dualPairing (hillHminusMiuraEnergyResidueHilbert C s n q (hr q hqC hreal))
                (hillHminusNumeratorHilbert D N (energy,q)) := by
  obtain ⟨δ,hδ,hδV,hδC,hcompat⟩ := hillHminus_period_data_canonical_compatibility C D E h0C hc hr
  refine ⟨δ,hδ,hδV,?_⟩
  intro q hq
  refine ⟨hδC hq,?_⟩
  intro hreal s n energy
  rw [(hcompat q hq hreal).2 energy]
  exact hillHminusMiuraEnergyPsi_eq_canonicalHilbert C s n q (hδC hq) (hr q (hδC hq) hreal) energy

end NLS.KdV
