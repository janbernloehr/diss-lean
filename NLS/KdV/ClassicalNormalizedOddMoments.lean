import NLS.KdV.ClassicalNormalizedMoments
import NLS.KdV.ClassicalHillOddDifferentialMoments
import NLS.KdV.ClassicalHillLowOddDifferentialMoments

/-! # Actual normalized odd moment cancellation on a common high tail

The entire normalized numerator is constructed from the same actual
inverse used for every normalization period. One complex potential
neighborhood and one cutoff precede all numerator and contour indices.
-/
noncomputable section
open Set Metric Complex NLS.LinearVolterra NLS.ComplexAnalysis
namespace NLS.KdV
namespace ClassicalAllContourPeriodData
variable {N : ℕ} {V : Set (Curve ℂ)} {A : ℝ}
variable (D : ClassicalAllContourPeriodData N V A)
include D

theorem exists_normalized_high_odd_moments
    (R : Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (hRa : AnalyticOnNhd ℂ R V) (q : Curve ℂ) (hq : q ∈ V) :
    ∃ M : ℕ, ∃ U : Set (Curve ℂ),
      0 < M ∧ U ⊆ V ∧ IsOpen U ∧ q ∈ U ∧
      (∀ n k : ℕ+, ∀ m : ℕ, AnalyticOnNhd ℂ (classicalHillNormalizedMoment N R n k m) U) ∧
      ∀ a ∈ U, ∀ n k : ℕ+, M ≤ (k : ℕ) → ∀ l : ℕ,
        classicalHillNormalizedMoment N R n k (2*l+1) a = 0 := by
  obtain ⟨M,W,hM,hW,hqW,hodd⟩ := exists_classicalHill_high_odd_differential_moments q
  refine ⟨M,V ∩ W,hM,inter_subset_left,D.isOpen.inter hW,⟨hq,hqW⟩,?_,?_⟩
  · intro n k m
    exact (D.normalizedMoment_analytic R hRa n k m).mono inter_subset_left
  intro a ha n k hk l
  simpa only [classicalHillNormalizedMoment,classicalHillNormalizedMomentIntegrand,classicalHillFrequencyPrimitive] using!
    hodd a ha.2 k hk (fun z => classicalHillNormalizedNumerator N R n (z,a))
      (D.normalizedNumerator_entire R hRa n a ha.1) l

/-- A single source neighborhood of zero supports every normalized odd
moment cancellation, before both positive indices and the moment order. -/
theorem exists_normalized_all_odd_moments
    (R : Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2)) (hRa : AnalyticOnNhd ℂ R V) :
    ∃ U : Set (Curve ℂ), U ⊆ V ∧ IsOpen U ∧ 0 ∈ U ∧
      (∀ n k : ℕ+, ∀ m : ℕ, AnalyticOnNhd ℂ (classicalHillNormalizedMoment N R n k m) U) ∧
      ∀ a ∈ U, ∀ n k : ℕ+, ∀ l : ℕ, classicalHillNormalizedMoment N R n k (2*l+1) a = 0 := by
  obtain ⟨W,hW,h0W,hodd⟩ := exists_classicalHill_all_odd_differential_moments
  refine ⟨V ∩ W,inter_subset_left,D.isOpen.inter hW,⟨D.zero_mem,h0W⟩,?_,?_⟩
  · intro n k m
    exact (D.normalizedMoment_analytic R hRa n k m).mono inter_subset_left
  intro a ha n k l
  simpa only [classicalHillNormalizedMoment,classicalHillNormalizedMomentIntegrand,classicalHillFrequencyPrimitive] using!
    hodd a ha.2 k (fun z => classicalHillNormalizedNumerator N R n (z,a))
      (D.normalizedNumerator_entire R hRa n a ha.1) l

end ClassicalAllContourPeriodData

/-- Actual normalized moments on one common neighborhood: all are analytic,
all zeroth moments have exact source normalization and every odd high-tail
moment vanishes, including the diagonal and collapsed gaps. -/
theorem exists_classicalHill_normalized_high_odd_moments :
    ∃ N M : ℕ, ∃ U : Set (Curve ℂ),
      ∃ R : Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2),
        0 < N ∧ 0 < M ∧ IsOpen U ∧ 0 ∈ U ∧ AnalyticOnNhd ℂ R U ∧
        R 0 = ContinuousLinearMap.id ℂ (NLS.Coeff 2) ∧
        (∀ n k : ℕ+, ∀ m : ℕ, AnalyticOnNhd ℂ (classicalHillNormalizedMoment N R n k m) U) ∧
        (∀ a ∈ U, ∀ n k : ℕ+,
          (2*(Real.pi : ℂ))⁻¹*classicalHillNormalizedMoment N R n k 0 a = if n = k then 1 else 0) ∧
        ∀ a ∈ U, ∀ n k : ℕ+, M ≤ (k : ℕ) → ∀ l : ℕ,
          classicalHillNormalizedMoment N R n k (2*l+1) a = 0 := by
  obtain ⟨N,V,T,R,hN,hV,h0V,_,hRa,_,hR0,hinv,hentry,A,D⟩ := exists_classicalHill_analytic_period_inverse
  obtain ⟨M,U,hM,hUV,hU,h0U,hma,hodd⟩ := D.exists_normalized_high_odd_moments R hRa 0 h0V
  refine ⟨N,M,U,R,hN,hM,hU,h0U,hRa.mono hUV,hR0,hma,?_,hodd⟩
  intro a ha n k
  exact D.normalizedMoment_zero_order R T n k a (hUV ha) (hentry a (hUV ha)) (hinv a (hUV ha)).1

/-- Actual normalized moments on one common neighborhood, before all
positive indices: analyticity, exact zeroth periods and every odd moment
cancellation. This includes all low contours and collapsed diagonal gaps. -/
theorem exists_classicalHill_normalized_all_odd_moments :
    ∃ N : ℕ, ∃ U : Set (Curve ℂ), ∃ R : Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2),
      0 < N ∧ IsOpen U ∧ 0 ∈ U ∧ AnalyticOnNhd ℂ R U ∧
      R 0 = ContinuousLinearMap.id ℂ (NLS.Coeff 2) ∧
      (∀ n k : ℕ+, ∀ m : ℕ, AnalyticOnNhd ℂ (classicalHillNormalizedMoment N R n k m) U) ∧
      (∀ a ∈ U, ∀ n k : ℕ+,
        (2*(Real.pi : ℂ))⁻¹*classicalHillNormalizedMoment N R n k 0 a = if n = k then 1 else 0) ∧
      ∀ a ∈ U, ∀ n k : ℕ+, ∀ l : ℕ, classicalHillNormalizedMoment N R n k (2*l+1) a = 0 := by
  obtain ⟨N,V,T,R,hN,_,_,_,hRa,_,hR0,hinv,hentry,A,D⟩ := exists_classicalHill_analytic_period_inverse
  obtain ⟨U,hUV,hU,h0U,hma,hodd⟩ := D.exists_normalized_all_odd_moments R hRa
  refine ⟨N,U,R,hN,hU,h0U,hRa.mono hUV,hR0,hma,?_,hodd⟩
  intro a ha n k
  exact D.normalizedMoment_zero_order R T n k a (hUV ha) (hentry a (hUV ha)) (hinv a (hUV ha)).1

end NLS.KdV
