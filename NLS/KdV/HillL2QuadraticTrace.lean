import NLS.KdV.HillFinitePhysicalPotential
import NLS.KdV.HillRealWeightedTruncation
import NLS.KdV.HillWeightedActionContinuity

/-! # The quadratic trace for actual real mean-zero L2 Hill actions

The smooth physical trace, exact finite Fourier normalization, real
mean-zero approximation and continuity of the full action sum prove the
quadratic trace on the entire native real mean-zero L2 coefficient domain.
The positive-index HasSum has exactly the source factor 2*pi*n.
-/

noncomputable section
open Set Complex Filter Topology MeasureTheory
open scoped ComplexConjugate ContDiff
namespace NLS.KdV

theorem tsum_hillWeightedActionTerm_finite_one
    (p : RealHillWeightedPotential SpectralWeight.one) (a : ℤ →₀ ℂ)
    (hp : p.val = WeightedCoeff.ofFinsupp SpectralWeight.one.doubleIndex.toWeight 2 a)
    (hmean : p.val.val 0 = 0) :
    (∑' n : ℕ, hillWeightedActionTerm SpectralWeight.one p n) = (1/2 : ℝ)*‖p.val‖^2 := by
  have ha (n : ℤ) : a (-n) = conj (a n) := by
    have h := p.property n
    simpa only [SpectralWeight.toCoeff_apply, hp, WeightedCoeff.ofFinsupp_apply] using h
  have haz : a 0 = 0 := by simpa only [hp, WeightedCoeff.ofFinsupp_apply] using hmean
  let Q := hillFinitePhysicalPotential a
  have hreal := real_hillFinitePhysicalPotential a ha
  have hperiodic := periodic_hillFinitePhysicalPotential a
  have hzero : (∫ x in (0 : ℝ)..1, Q (x : AddCircle (2 : ℝ))) = 0 :=
    (mean_hillFinitePhysicalPotential a).trans haz
  have h := hasSum_hillRealActions_half_integral_norm_sq_smooth Q hreal
    (contDiff_hillFinitePhysicalPotential a) hperiodic hzero
  have hcoeff : hillContinuousCoefficients Q = hillPeriodOneUnitPotential SpectralWeight.one p.val := by
    rw [hp]
    exact hillContinuousCoefficients_finitePhysical a
  have he (k : ℕ) : (2*(k+1 : ℕ)*Real.pi : ℝ) *
      hillRealGapIntegral (hillContinuousCoefficients Q) (hillContinuousCoefficients_mem_even Q hperiodic)
        (isRealHillPotential_hillContinuousCoefficients Q hreal) (k+1) 0 =
      hillWeightedActionTerm SpectralWeight.one p (k+1) := by
    rw [hillWeightedActionTerm, SpectralWeight.one_apply, one_pow, one_mul, hillPeriodOneAction]
    rw [hillRealGapIntegral_congr (hillContinuousCoefficients Q)
      (hillPeriodOneUnitPotential SpectralWeight.one p.val)
      (hillContinuousCoefficients_mem_even Q hperiodic)
      (hillPeriodOneUnitPotential_even SpectralWeight.one p.val)
      (isRealHillPotential_hillContinuousCoefficients Q hreal)
      (hillPeriodOneUnitPotential_real SpectralWeight.one p.val p.property) hcoeff (k+1) 0]
    congr 1
    push_cast
    ring
  have hefun := funext he
  rw [hefun] at h
  have hnorm : (∫ x in (0 : ℝ)..1, ‖Q (x : AddCircle (2 : ℝ))‖^2) = ‖p.val‖^2 := by
    have heQ (x : ℝ) : Q (x : AddCircle (2 : ℝ)) = Fourier.polynomial a x :=
      congrFun (hillFinitePhysicalPotential_coe a) x
    simp_rw [heQ]
    rw [Fourier.integral_sq_polynomial, hp, norm_sq_hillFiniteNative]
  rw [hnorm] at h
  have hz : hillWeightedActionTerm SpectralWeight.one p 0 = 0 := by simp [hillWeightedActionTerm]
  have ht := (summable_hillWeightedActionTerm SpectralWeight.one p).sum_add_tsum_nat_add 1
  have he0 : (∑' n : ℕ, hillWeightedActionTerm SpectralWeight.one p n) =
      ∑' k : ℕ, hillWeightedActionTerm SpectralWeight.one p (k+1) := by
    simpa only [Finset.sum_range_one, hz, zero_add] using ht.symm
  exact he0.trans h.tsum_eq

theorem tsum_hillWeightedActionTerm_quadratic_l2
    (q : RealHillWeightedPotential SpectralWeight.one) (hmean : q.val.val 0 = 0) :
    (∑' n : ℕ, hillWeightedActionTerm SpectralWeight.one q n) = (1/2 : ℝ)*‖q.val‖^2 := by
  have hfinite (N : ℕ) :
      (∑' n : ℕ, hillWeightedActionTerm SpectralWeight.one
        (hillRealWeightedTruncate SpectralWeight.one N q) n) =
      (1/2 : ℝ)*‖(hillRealWeightedTruncate SpectralWeight.one N q).val‖^2 :=
    tsum_hillWeightedActionTerm_finite_one _
      (hillRealTruncationFinsupp SpectralWeight.one N q)
      (hillRealWeightedTruncate_eq_ofFinsupp SpectralWeight.one N q)
      (hillRealWeightedTruncate_mean_zero SpectralWeight.one N q hmean)
  have hq := tendsto_hillRealWeightedTruncate SpectralWeight.one q
  have ht := ((continuous_tsum_hillWeightedActionTerm SpectralWeight.one).tendsto q).comp hq
  have hn : Tendsto (fun N : ℕ => (1/2 : ℝ)*‖(hillRealWeightedTruncate SpectralWeight.one N q).val‖^2)
      atTop (𝓝 ((1/2 : ℝ)*‖q.val‖^2)) := by
    have hc : Continuous (fun p : RealHillWeightedPotential SpectralWeight.one => (1/2 : ℝ)*‖p.val‖^2) :=
      (continuous_subtype_val.norm.pow 2).const_mul _
    exact (hc.tendsto q).comp hq
  have he : (fun N : ℕ => ∑' n : ℕ, hillWeightedActionTerm SpectralWeight.one
      (hillRealWeightedTruncate SpectralWeight.one N q) n) =
      (fun N : ℕ => (1/2 : ℝ)*‖(hillRealWeightedTruncate SpectralWeight.one N q).val‖^2) :=
    funext hfinite
  simp only [Function.comp_def] at ht
  rw [he] at ht
  exact tendsto_nhds_unique ht hn


theorem hasSum_hillPeriodOneActions_quadratic_l2
    (q : RealHillWeightedPotential SpectralWeight.one) (hmean : q.val.val 0 = 0) :
    HasSum (fun k : ℕ => (2 * Real.pi * (k+1 : ℕ)) *
      hillPeriodOneAction SpectralWeight.one q.val q.property (k+1)) ((1/2 : ℝ)*‖q.val‖^2) := by
  have hs : Summable (fun k : ℕ => hillWeightedActionTerm SpectralWeight.one q (k+1)) :=
    (summable_nat_add_iff 1).mpr (summable_hillWeightedActionTerm SpectralWeight.one q)
  have hz : hillWeightedActionTerm SpectralWeight.one q 0 = 0 := by simp [hillWeightedActionTerm]
  have ht := (summable_hillWeightedActionTerm SpectralWeight.one q).sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one, hz, zero_add] at ht
  have hv : (∑' k : ℕ, hillWeightedActionTerm SpectralWeight.one q (k+1)) =
      (1/2 : ℝ)*‖q.val‖^2 := ht.trans (tsum_hillWeightedActionTerm_quadratic_l2 q hmean)
  have h := hs.hasSum
  rw [hv] at h
  simpa only [hillWeightedActionTerm, SpectralWeight.one_apply, one_pow, one_mul] using h

theorem hasSum_hillNativeGapIntegrals_quadratic_l2
    (q : WeightedCoeff SpectralWeight.one.doubleIndex.toWeight 2)
    (hr : IsRealHillPotential (SpectralWeight.one.doubleIndex.toCoeff q))
    (hmean : q.val 0 = 0) :
    HasSum (fun k : ℕ => (2 * Real.pi * (k+1 : ℕ)) *
      hillRealGapIntegral (hillPeriodOneUnitPotential SpectralWeight.one q)
        (hillPeriodOneUnitPotential_even SpectralWeight.one q)
        (hillPeriodOneUnitPotential_real SpectralWeight.one q hr) (k+1) 0) ((1/2 : ℝ)*‖q‖^2) :=
  hasSum_hillPeriodOneActions_quadratic_l2 ⟨q, hr⟩ hmean

end NLS.KdV
