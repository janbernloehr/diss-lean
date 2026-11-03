import NLS.KdV.HillSobolevTraceFamily
import NLS.KdV.HillSmoothHierarchyTrace
import NLS.KdV.HillH1EnergyTrace

/-! # The complete actual hierarchy moment trace on every real mean-zero sharp Sobolev domain. -/

noncomputable section
open Set Complex MeasureTheory Filter Topology
open NLS.Fourier NLS.ZakharovShabat
open scoped ComplexConjugate
namespace NLS.KdV
theorem tsum_hillHierarchyMomentTerm_hierarchy_finite (m : ℕ)
    (p : RealHillWeightedPotential (hillIntegerWeight m)) (a : ℤ →₀ ℂ)
    (hp : p.val = WeightedCoeff.ofFinsupp (hillIntegerWeight m).doubleIndex.toWeight 2 a)
    (hmean : p.val.val 0 = 0) :
    ((∑' n : ℕ, hillHierarchyMomentTerm (hillIntegerWeight m) p m n : ℝ) : ℂ) =
      hillNativeHierarchyTraceValue m p.val := by
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
  have hcoeff : hillContinuousCoefficients Q = hillPeriodOneUnitPotential (hillIntegerWeight m) p.val := by
    rw [hp]
    exact hillContinuousCoefficients_finitePhysical_weighted _ a
  have he (k : ℕ) : (2*(k+1 : ℕ)*Real.pi : ℂ) *
      hillL2RealContourMoment (hillContinuousCoefficients Q) (hillContinuousCoefficients_mem_even Q hperiodic)
        (isRealHillPotential_hillContinuousCoefficients Q hreal) (k+1) m =
      (hillHierarchyMomentTerm (hillIntegerWeight m) p m (k+1) : ℂ) := by
    rw [hillL2RealContourMoment_eq_gapIntegral _ _ _ (k+1) (by omega)]
    rw [hillRealGapIntegral_congr (hillContinuousCoefficients Q)
      (hillPeriodOneUnitPotential (hillIntegerWeight m) p.val)
      (hillContinuousCoefficients_mem_even Q hperiodic)
      (hillPeriodOneUnitPotential_even (hillIntegerWeight m) p.val)
      (isRealHillPotential_hillContinuousCoefficients Q hreal)
      (hillPeriodOneUnitPotential_real (hillIntegerWeight m) p.val p.property) hcoeff (k+1) m]
    unfold hillHierarchyMomentTerm
    push_cast
    ring
  rw [funext he] at h
  have hE : hillNativeHierarchyTraceValue m p.val = hillClassicalHierarchyTraceValue
      (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) m := by
    unfold hillNativeHierarchyTraceValue
    apply hillSobolevTraceValue_eq_classical m m le_rfl _ _
      (contDiff_hillFinitePhysicalPotential a) hperiodic
    intro k
    rw [hillNativeIntegerToScalar_apply, hp]
    have hc := periodOneCoefficient_synthesis (Coeff.ofFinsupp (p := 1) a) k
    change a k = periodOneCoefficient (periodOneSynthesis (Coeff.ofFinsupp (p := 1) a)) k
    exact hc.symm
  rw [← hE] at h
  have hs := summable_hillHierarchyMomentTerm (hillIntegerWeight m) p m
    (fun n _ => hillIntegerWeight_growth m n)
  have hz : hillHierarchyMomentTerm (hillIntegerWeight m) p m 0 = 0 := by simp [hillHierarchyMomentTerm]
  have ht := hs.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one, hz, zero_add] at ht
  have hpos := ((summable_nat_add_iff 1).mpr hs).hasSum
  rw [ht] at hpos
  have hc : HasSum (fun k : ℕ => (hillHierarchyMomentTerm (hillIntegerWeight m) p m (k+1) : ℂ))
      ((∑' n : ℕ, hillHierarchyMomentTerm (hillIntegerWeight m) p m n : ℝ) : ℂ) := by
    simpa only [Complex.ofRealCLM_apply] using Complex.ofRealCLM.hasSum hpos
  exact hc.unique h

theorem tsum_hillHierarchyMomentTerm_hierarchy_sobolev (m : ℕ)
    (q : RealHillWeightedPotential (hillIntegerWeight m)) (hmean : q.val.val 0 = 0) :
    ((∑' n : ℕ, hillHierarchyMomentTerm (hillIntegerWeight m) q m n : ℝ) : ℂ) =
      hillNativeHierarchyTraceValue m q.val := by
  have hfinite (N : ℕ) :
      ((∑' n : ℕ, hillHierarchyMomentTerm (hillIntegerWeight m)
        (hillRealWeightedTruncate (hillIntegerWeight m) N q) m n : ℝ) : ℂ) =
      hillNativeHierarchyTraceValue m (hillRealWeightedTruncate (hillIntegerWeight m) N q).val :=
    tsum_hillHierarchyMomentTerm_hierarchy_finite m _ (hillRealTruncationFinsupp (hillIntegerWeight m) N q)
      (hillRealWeightedTruncate_eq_ofFinsupp (hillIntegerWeight m) N q)
      (hillRealWeightedTruncate_mean_zero (hillIntegerWeight m) N q hmean)
  have hq := tendsto_hillRealWeightedTruncate (hillIntegerWeight m) q
  have hL : Continuous (fun p : RealHillWeightedPotential (hillIntegerWeight m) =>
      ((∑' n : ℕ, hillHierarchyMomentTerm (hillIntegerWeight m) p m n : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_tsum_hillHierarchyMomentTerm (hillIntegerWeight m) m
      (fun n _ => hillIntegerWeight_growth m n))
  have hR : Continuous (fun p : RealHillWeightedPotential (hillIntegerWeight m) => hillNativeHierarchyTraceValue m p.val) :=
    (continuous_hillNativeHierarchyTraceValue m).comp continuous_subtype_val
  have hLt := (hL.tendsto q).comp hq
  have hRt := (hR.tendsto q).comp hq
  simp only [Function.comp_def] at hLt hRt
  rw [funext hfinite] at hLt
  exact tendsto_nhds_unique hLt hRt


theorem hasSum_hillHierarchyMoments_hierarchy_sobolev (m : ℕ)
    (q : RealHillWeightedPotential (hillIntegerWeight m)) (hmean : q.val.val 0 = 0) :
    HasSum (fun k : ℕ => hillHierarchyMomentTerm (hillIntegerWeight m) q m (k+1))
      ((hillNativeHierarchyTraceValue m q.val).re) := by
  have hs := summable_hillHierarchyMomentTerm (hillIntegerWeight m) q m
    (fun n _ => hillIntegerWeight_growth m n)
  have hz : hillHierarchyMomentTerm (hillIntegerWeight m) q m 0 = 0 := by simp [hillHierarchyMomentTerm]
  have ht := hs.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one, hz, zero_add] at ht
  have hv := congrArg Complex.re (tsum_hillHierarchyMomentTerm_hierarchy_sobolev m q hmean)
  simp only [Complex.ofReal_re] at hv
  have h := ((summable_nat_add_iff 1).mpr hs).hasSum
  rw [ht, hv] at h
  exact h


end NLS.KdV

namespace NLS.KdV
open Complex NLS.Fourier NLS.ZakharovShabat
open scoped ComplexConjugate

theorem hasSum_hillNativeMoments_hierarchy (m : ℕ)
    (q : WeightedCoeff (hillIntegerWeight m).doubleIndex.toWeight 2)
    (hr : IsRealHillPotential ((hillIntegerWeight m).doubleIndex.toCoeff q))
    (hmean : q.val 0 = 0) :
    HasSum (fun k : ℕ => (2*Real.pi*(k+1 : ℕ)) *
      hillRealGapIntegral (hillPeriodOneUnitPotential (hillIntegerWeight m) q)
        (hillPeriodOneUnitPotential_even (hillIntegerWeight m) q)
        (hillPeriodOneUnitPotential_real (hillIntegerWeight m) q hr) (k+1) m)
      ((hillNativeHierarchyTraceValue m q).re) := by
  have h := hasSum_hillHierarchyMoments_hierarchy_sobolev m ⟨q,hr⟩ hmean
  simpa only [hillHierarchyMomentTerm] using h

theorem isReal_hillScalarToNativeInteger (m : ℕ) (a : ScalarSobolev m)
    (hr : ∀ k, a.val (-k) = conj (a.val k)) :
    IsRealHillPotential ((hillIntegerWeight m).doubleIndex.toCoeff (hillScalarToNativeInteger m a)) := by
  intro k
  simpa only [SpectralWeight.toCoeff_apply, hillScalarToNativeInteger_apply] using hr k

theorem hasSum_hillSharedSobolevMoments_hierarchy (m : ℕ) (a : ScalarSobolev m)
    (hr : ∀ k, a.val (-k) = conj (a.val k)) (hmean : a.val 0 = 0) :
    HasSum (fun k : ℕ => (2*Real.pi*(k+1 : ℕ)) *
      hillRealGapIntegral (hillPeriodOneUnitPotential (hillIntegerWeight m) (hillScalarToNativeInteger m a))
        (hillPeriodOneUnitPotential_even (hillIntegerWeight m) (hillScalarToNativeInteger m a))
        (hillPeriodOneUnitPotential_real (hillIntegerWeight m) (hillScalarToNativeInteger m a)
          (isReal_hillScalarToNativeInteger m a hr)) (k+1) m)
      ((hillSobolevTraceValue m m a).re) := by
  have h := hasSum_hillNativeMoments_hierarchy m (hillScalarToNativeInteger m a)
    (isReal_hillScalarToNativeInteger m a hr) (by simpa only [hillScalarToNativeInteger_apply] using hmean)
  simpa only [hillNativeHierarchyTraceValue, hillNativeIntegerToScalar_scalarToNativeInteger] using h

theorem hillNativeHierarchyTraceValue_im_eq_zero (m : ℕ)
    (q : RealHillWeightedPotential (hillIntegerWeight m)) (hmean : q.val.val 0 = 0) :
    (hillNativeHierarchyTraceValue m q.val).im = 0 := by
  have h := congrArg Complex.im (tsum_hillHierarchyMomentTerm_hierarchy_sobolev m q hmean)
  simpa only [Complex.ofReal_im] using h.symm

theorem hillScalarSobolevLower_self (m : ℕ) (a : ScalarSobolev m) :
    hillScalarSobolevLower m m le_rfl a = a := by
  apply Subtype.ext
  funext k
  rw [hillScalarSobolevLower_apply]

theorem hillSobolevHamiltonianFamily_self (m : ℕ) (hm : 1 ≤ m) (a : ScalarSobolev m) :
    hillSobolevHamiltonianFamily m a m = hillSobolevHamiltonian m hm a := by
  rw [hillSobolevHamiltonianFamily, dif_pos le_rfl, hillSobolevHamiltonianAt,
    dif_neg (by omega : m ≠ 0), hillScalarSobolevLower_self]

end NLS.KdV

noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory Filter Topology NLS.Fourier NLS.ZakharovShabat
open scoped ComplexConjugate
namespace NLS.KdV

def hillSharedPhysicalPotential (m : ℕ) (hm : 1 ≤ m) (a : ScalarSobolev m) :
    C(AddCircle (2 : ℝ), ℂ) :=
  periodOneSobolevSynthesis (hierarchySobolevToScalarDomain m hm a)

theorem hillContinuousCoefficients_sharedPhysical (m : ℕ) (hm : 1 ≤ m) (a : ScalarSobolev m) :
    hillContinuousCoefficients (hillSharedPhysicalPotential m hm a) =
      hillPeriodOneUnitPotential (hillIntegerWeight m) (hillScalarToNativeInteger m a) := by
  let b := hierarchySobolevToScalarDomain m hm a
  have hc := hillContinuousCoefficients_nativeH1 (hillScalarToNativeH1 b)
  rw [hillNativeH1ToScalar_scalarToNativeH1] at hc
  apply hc.trans
  apply hillPeriodOneUnitPotential_eq_of_coeff_eq
  intro k
  rw [hillScalarToNativeH1_apply, hillScalarToNativeInteger_apply]
  exact hierarchySobolevToScalarDomain_apply m hm a k

theorem hillSharedPhysicalPotential_periodic (m : ℕ) (hm : 1 ≤ m) (a : ScalarSobolev m) :
    Function.Periodic (fun x : ℝ => hillSharedPhysicalPotential m hm a (x : AddCircle (2 : ℝ))) 1 :=
  periodOneSobolevSynthesis_periodic _

theorem hillSharedPhysicalPotential_mean (m : ℕ) (hm : 1 ≤ m) (a : ScalarSobolev m) :
    (∫ x in (0 : ℝ)..1, hillSharedPhysicalPotential m hm a (x : AddCircle (2 : ℝ))) = a.val 0 := by
  exact (mean_periodOneSobolevSynthesis (hierarchySobolevToScalarDomain m hm a)).trans
    (hierarchySobolevToScalarDomain_apply m hm a 0)

theorem hillSharedPhysicalPotential_real_coefficients (m : ℕ) (hm : 1 ≤ m) (a : ScalarSobolev m)
    (hreal : ∀ x : AddCircle (2 : ℝ), (hillSharedPhysicalPotential m hm a x).im = 0) :
    ∀ k, a.val (-k) = conj (a.val k) := by
  have hr := isReal_scalarInclusion_of_physical_real (hierarchySobolevToScalarDomain m hm a) hreal
  intro k
  simpa only [scalarInclusion_apply, hierarchySobolevToScalarDomain_apply] using hr k

theorem hasSum_hillPhysicalSobolevMoments_hierarchy (m : ℕ) (hm : 1 ≤ m) (a : ScalarSobolev m)
    (hreal : ∀ x : AddCircle (2 : ℝ), (hillSharedPhysicalPotential m hm a x).im = 0)
    (hmean : (∫ x in (0 : ℝ)..1, hillSharedPhysicalPotential m hm a (x : AddCircle (2 : ℝ))) = 0) :
    let Q := hillSharedPhysicalPotential m hm a
    HasSum (fun k : ℕ => (2*Real.pi*(k+1 : ℕ)) *
      hillRealGapIntegral (hillContinuousCoefficients Q)
        (hillContinuousCoefficients_mem_even Q (hillSharedPhysicalPotential_periodic m hm a))
        (isRealHillPotential_hillContinuousCoefficients Q hreal) (k+1) m)
      ((hillSobolevTraceValue m m a).re) := by
  dsimp only
  let Q := hillSharedPhysicalPotential m hm a
  let p := hillScalarToNativeInteger m a
  have hra := hillSharedPhysicalPotential_real_coefficients m hm a hreal
  have hzero : a.val 0 = 0 := (hillSharedPhysicalPotential_mean m hm a).symm.trans hmean
  have hp := isReal_hillScalarToNativeInteger m a hra
  have h := hasSum_hillSharedSobolevMoments_hierarchy m a hra hzero
  have hc : hillContinuousCoefficients Q = hillPeriodOneUnitPotential (hillIntegerWeight m) p :=
    hillContinuousCoefficients_sharedPhysical m hm a
  have he (k : ℕ) : hillRealGapIntegral (hillPeriodOneUnitPotential (hillIntegerWeight m) p)
      (hillPeriodOneUnitPotential_even (hillIntegerWeight m) p)
      (hillPeriodOneUnitPotential_real (hillIntegerWeight m) p hp) (k+1) m =
    hillRealGapIntegral (hillContinuousCoefficients Q)
      (hillContinuousCoefficients_mem_even Q (hillSharedPhysicalPotential_periodic m hm a))
      (isRealHillPotential_hillContinuousCoefficients Q hreal) (k+1) m :=
    hillRealGapIntegral_congr _ _ _ _ _ _ hc.symm (k+1) m
  have hefun : (fun k : ℕ => (2*Real.pi*(k+1 : ℕ)) *
      hillRealGapIntegral (hillPeriodOneUnitPotential (hillIntegerWeight m) p)
        (hillPeriodOneUnitPotential_even (hillIntegerWeight m) p)
        (hillPeriodOneUnitPotential_real (hillIntegerWeight m) p hp) (k+1) m) =
      (fun k : ℕ => (2*Real.pi*(k+1 : ℕ)) *
        hillRealGapIntegral (hillContinuousCoefficients Q)
          (hillContinuousCoefficients_mem_even Q (hillSharedPhysicalPotential_periodic m hm a))
          (isRealHillPotential_hillContinuousCoefficients Q hreal) (k+1) m) := by
    funext k
    rw [he k]
  rw [hefun] at h
  exact h

end NLS.KdV
