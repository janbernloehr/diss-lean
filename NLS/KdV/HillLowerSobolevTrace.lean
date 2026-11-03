import NLS.KdV.HillUniformMomentComparison

/-! # Actual lower moment traces and monotone action masses on a fixed sharp Sobolev domain. -/

noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory Filter Topology NLS.Fourier NLS.ZakharovShabat
open scoped ComplexConjugate
namespace NLS.KdV
theorem tsum_hillHierarchyMomentTerm_hierarchy_finite_of_le (M m : ℕ) (hm : m ≤ M)
    (p : RealHillWeightedPotential (hillIntegerWeight M)) (a : ℤ →₀ ℂ)
    (hp : p.val = WeightedCoeff.ofFinsupp (hillIntegerWeight M).doubleIndex.toWeight 2 a)
    (hmean : p.val.val 0 = 0) :
    ((∑' n : ℕ, hillHierarchyMomentTerm (hillIntegerWeight M) p m n : ℝ) : ℂ) =
      hillSobolevTraceValue M m (hillNativeIntegerToScalar M p.val) := by
  have ha (n : ℤ) : a (-n) = conj (a n) := by
    have h := p.property n
    simpa only [SpectralWeight.toCoeff_apply, hp, WeightedCoeff.ofFinsupp_apply] using h
  have haz : a 0 = 0 := by simpa only [hp, WeightedCoeff.ofFinsupp_apply] using hmean
  let Q := hillFinitePhysicalPotential a
  have hreal := real_hillFinitePhysicalPotential a ha
  have hperiodic := periodic_hillFinitePhysicalPotential a
  have hzero : (∫ x in (0 : ℝ)..1, Q (x : AddCircle (2 : ℝ))) = 0 :=
    (mean_hillFinitePhysicalPotential a).trans haz
  have h := hasSum_hillPhysicalMoments_hierarchy_smooth Q hreal
    (contDiff_hillFinitePhysicalPotential a) hperiodic hzero m
  have hcoeff : hillContinuousCoefficients Q = hillPeriodOneUnitPotential (hillIntegerWeight M) p.val := by
    rw [hp]
    exact hillContinuousCoefficients_finitePhysical_weighted _ a
  have he (k : ℕ) : (2*(k+1 : ℕ)*Real.pi : ℂ) *
      hillL2RealContourMoment (hillContinuousCoefficients Q) (hillContinuousCoefficients_mem_even Q hperiodic)
        (isRealHillPotential_hillContinuousCoefficients Q hreal) (k+1) m =
      (hillHierarchyMomentTerm (hillIntegerWeight M) p m (k+1) : ℂ) := by
    rw [hillL2RealContourMoment_eq_gapIntegral _ _ _ (k+1) (by omega)]
    rw [hillRealGapIntegral_congr (hillContinuousCoefficients Q)
      (hillPeriodOneUnitPotential (hillIntegerWeight M) p.val)
      (hillContinuousCoefficients_mem_even Q hperiodic)
      (hillPeriodOneUnitPotential_even (hillIntegerWeight M) p.val)
      (isRealHillPotential_hillContinuousCoefficients Q hreal)
      (hillPeriodOneUnitPotential_real (hillIntegerWeight M) p.val p.property) hcoeff (k+1) m]
    unfold hillHierarchyMomentTerm
    push_cast
    ring
  rw [funext he] at h
  have hE : hillSobolevTraceValue M m (hillNativeIntegerToScalar M p.val) = hillClassicalHierarchyTraceValue
      (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) m := by
    apply hillSobolevTraceValue_eq_classical M m hm _ _
      (contDiff_hillFinitePhysicalPotential a) hperiodic
    intro k
    rw [hillNativeIntegerToScalar_apply, hp]
    have hc := periodOneCoefficient_synthesis (Coeff.ofFinsupp (p := 1) a) k
    change a k = periodOneCoefficient (periodOneSynthesis (Coeff.ofFinsupp (p := 1) a)) k
    exact hc.symm
  rw [← hE] at h
  have hs := summable_hillHierarchyMomentTerm (hillIntegerWeight M) p m
    (fun n hn => hillIntegerWeight_growth_of_le M m hm n hn)
  have hz : hillHierarchyMomentTerm (hillIntegerWeight M) p m 0 = 0 := by simp [hillHierarchyMomentTerm]
  have ht := hs.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one, hz, zero_add] at ht
  have hpos := ((summable_nat_add_iff 1).mpr hs).hasSum
  rw [ht] at hpos
  have hc : HasSum (fun k : ℕ => (hillHierarchyMomentTerm (hillIntegerWeight M) p m (k+1) : ℂ))
      ((∑' n : ℕ, hillHierarchyMomentTerm (hillIntegerWeight M) p m n : ℝ) : ℂ) := by
    simpa only [Complex.ofRealCLM_apply] using Complex.ofRealCLM.hasSum hpos
  exact hc.unique h

theorem tsum_hillHierarchyMomentTerm_hierarchy_sobolev_of_le (M m : ℕ) (hm : m ≤ M)
    (q : RealHillWeightedPotential (hillIntegerWeight M)) (hmean : q.val.val 0 = 0) :
    ((∑' n : ℕ, hillHierarchyMomentTerm (hillIntegerWeight M) q m n : ℝ) : ℂ) =
      hillSobolevTraceValue M m (hillNativeIntegerToScalar M q.val) := by
  have hfinite (N : ℕ) :
      ((∑' n : ℕ, hillHierarchyMomentTerm (hillIntegerWeight M)
        (hillRealWeightedTruncate (hillIntegerWeight M) N q) m n : ℝ) : ℂ) =
      hillSobolevTraceValue M m (hillNativeIntegerToScalar M (hillRealWeightedTruncate (hillIntegerWeight M) N q).val) :=
    tsum_hillHierarchyMomentTerm_hierarchy_finite_of_le M m hm _ (hillRealTruncationFinsupp (hillIntegerWeight M) N q)
      (hillRealWeightedTruncate_eq_ofFinsupp (hillIntegerWeight M) N q)
      (hillRealWeightedTruncate_mean_zero (hillIntegerWeight M) N q hmean)
  have hq := tendsto_hillRealWeightedTruncate (hillIntegerWeight M) q
  have hL : Continuous (fun p : RealHillWeightedPotential (hillIntegerWeight M) =>
      ((∑' n : ℕ, hillHierarchyMomentTerm (hillIntegerWeight M) p m n : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_tsum_hillHierarchyMomentTerm (hillIntegerWeight M) m
      (fun n hn => hillIntegerWeight_growth_of_le M m hm n hn))
  have hR : Continuous (fun p : RealHillWeightedPotential (hillIntegerWeight M) => hillSobolevTraceValue M m (hillNativeIntegerToScalar M p.val)) :=
    ((continuous_hillSobolevTraceValue M m).comp (hillNativeIntegerToScalar M).continuous).comp continuous_subtype_val
  have hLt := (hL.tendsto q).comp hq
  have hRt := (hR.tendsto q).comp hq
  simp only [Function.comp_def] at hLt hRt
  rw [funext hfinite] at hLt
  exact tendsto_nhds_unique hLt hRt


theorem hillGapActionTerm_mono_order
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (j k : ℕ) (hjk : j ≤ k) (n : ℕ) :
    hillGapActionTerm q hq hr j n ≤ hillGapActionTerm q hq hr k n := by
  by_cases hn : n = 0
  · subst n; simp
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hfreq : 1 ≤ 2*Real.pi*(n : ℝ) := by nlinarith [Real.pi_gt_three]
    rw [hillGapActionTerm_factor q hq hr j n, hillGapActionTerm_factor q hq hr k n]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ hfreq (by omega : 2*j ≤ 2*k))
      (hillGapActionTerm_nonneg q hq hr 0 n)

theorem tsum_hillNativeGapActions_mono_order (M j k : ℕ) (hjk : j ≤ k) (hk : k ≤ M)
    (p : RealHillWeightedPotential (hillIntegerWeight M)) :
    let q := hillPeriodOneUnitPotential (hillIntegerWeight M) p.val
    let hq := hillPeriodOneUnitPotential_even (hillIntegerWeight M) p.val
    let hr := hillPeriodOneUnitPotential_real (hillIntegerWeight M) p.val p.property
    (∑' n, hillGapActionTerm q hq hr j n) ≤ ∑' n, hillGapActionTerm q hq hr k n := by
  dsimp only
  exact (summable_hillNativeGapActions M j (hjk.trans hk) p).tsum_le_tsum
    (hillGapActionTerm_mono_order _ _ _ j k hjk) (summable_hillNativeGapActions M k hk p)

theorem hillHierarchyHamiltonian_eq_trace_add_convolution (H : ℕ → ℂ) (m : ℕ) :
    H m = 4^m*hillHierarchyTraceCoefficient H m +
      2*(if 2 ≤ m then ∑ ij ∈ Finset.antidiagonal (m-2), H ij.1*H ij.2 else 0) := by
  unfold hillHierarchyTraceCoefficient
  have h4 : (4 : ℂ)^m ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp
  ring


theorem norm_hillHierarchyHamiltonian_le_trace_convolution (H : ℕ → ℂ) (m : ℕ) :
    ‖H m‖ ≤ (4 : ℝ)^m*‖hillHierarchyTraceCoefficient H m‖+
      2*(if 2 ≤ m then ∑ ik ∈ Finset.antidiagonal (m-2), ‖H ik.1‖*‖H ik.2‖ else 0) := by
  have hc : ‖(if 2 ≤ m then ∑ ik ∈ Finset.antidiagonal (m-2), H ik.1*H ik.2 else 0)‖ ≤
      if 2 ≤ m then ∑ ik ∈ Finset.antidiagonal (m-2), ‖H ik.1‖*‖H ik.2‖ else 0 := by
    split_ifs
    · simpa only [norm_mul] using norm_sum_le (Finset.antidiagonal (m-2)) (fun ik => H ik.1*H ik.2)
    · simp
  calc
    _ = ‖4^m*hillHierarchyTraceCoefficient H m+
        2*(if 2 ≤ m then ∑ ik ∈ Finset.antidiagonal (m-2), H ik.1*H ik.2 else 0)‖ :=
      congrArg norm (hillHierarchyHamiltonian_eq_trace_add_convolution H m)
    _ ≤ ‖4^m*hillHierarchyTraceCoefficient H m‖+
        ‖2*(if 2 ≤ m then ∑ ik ∈ Finset.antidiagonal (m-2), H ik.1*H ik.2 else 0)‖ := norm_add_le _ _
    _ ≤ _ := by
      simp only [norm_mul, norm_pow, Complex.norm_ofNat]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hc (show (0 : ℝ) ≤ 2 by norm_num))


theorem norm_hillSobolevHamiltonianFamily_le_moment_convolution (M m : ℕ) (hm : m ≤ M)
    (p : RealHillWeightedPotential (hillIntegerWeight M)) (hmean : p.val.val 0 = 0) :
    let H := hillSobolevHamiltonianFamily M (hillNativeIntegerToScalar M p.val)
    ‖H m‖ ≤ (4 : ℝ)^m*(∑' n, |hillHierarchyMomentTerm (hillIntegerWeight M) p m n|)+
      2*(if 2 ≤ m then ∑ ik ∈ Finset.antidiagonal (m-2), ‖H ik.1‖*‖H ik.2‖ else 0) := by
  dsimp only
  have ht := tsum_hillHierarchyMomentTerm_hierarchy_sobolev_of_le M m hm p hmean
  unfold hillSobolevTraceValue at ht
  have h := norm_hillHierarchyHamiltonian_le_trace_convolution
    (hillSobolevHamiltonianFamily M (hillNativeIntegerToScalar M p.val)) m
  rw [← ht, Complex.norm_real] at h
  have hs := summable_hillHierarchyMomentTerm (hillIntegerWeight M) p m
    (fun n hn => hillIntegerWeight_growth_of_le M m hm n hn)
  have hb := norm_tsum_le_tsum_norm hs.norm
  simp only [Real.norm_eq_abs] at hb h
  exact h.trans (add_le_add (mul_le_mul_of_nonneg_left hb (show (0 : ℝ) ≤ 4^m by positivity)) le_rfl)


end NLS.KdV
