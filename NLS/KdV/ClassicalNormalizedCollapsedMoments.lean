import NLS.KdV.ClassicalNormalizedOddMoments
import NLS.KdV.ClassicalHillCollapsedDifferentialMoments

/-! # Actual normalized positive moments at collapsed high gaps

The analytic inverse and the original periods are retained. The collapsed
criterion is the actual analytic squared Hill gap, rather than an assumed
removable integrand or an open-gap lower bound.
-/
noncomputable section
open Set Metric Complex NLS.LinearVolterra NLS.ComplexAnalysis
namespace NLS.KdV
namespace ClassicalAllContourPeriodData
variable {N : ℕ} {V : Set (Curve ℂ)} {A : ℝ}
variable (D : ClassicalAllContourPeriodData N V A)
include D

theorem exists_normalized_high_collapsed_moments
    (R : Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (hRa : AnalyticOnNhd ℂ R V) (q : Curve ℂ) (hq : q ∈ V) :
    ∃ M : ℕ, ∃ U : Set (Curve ℂ), 0 < M ∧ U ⊆ V ∧ IsOpen U ∧ q ∈ U ∧
      (∀ n k : ℕ+, ∀ m : ℕ, AnalyticOnNhd ℂ (classicalHillNormalizedMoment N R n k m) U) ∧
      ∀ a ∈ U, ∀ n k : ℕ+, M ≤ (k : ℕ) → classicalHillHighSquaredGap a k = 0 → ∀ m : ℕ,
        classicalHillNormalizedMoment N R n k (m+1) a = 0 := by
  obtain ⟨M,W,hM,hW,hqW,hclosed⟩ := exists_classicalHill_high_collapsed_differential_moments q
  refine ⟨M,V ∩ W,hM,inter_subset_left,D.isOpen.inter hW,⟨hq,hqW⟩,?_,?_⟩
  · intro n k m
    exact (D.normalizedMoment_analytic R hRa n k m).mono inter_subset_left
  intro a ha n k hk hgap m
  simpa only [classicalHillNormalizedMoment,classicalHillNormalizedMomentIntegrand,classicalHillFrequencyPrimitive] using!
    hclosed a ha.2 k hk hgap (fun z => classicalHillNormalizedNumerator N R n (z,a))
      (D.normalizedNumerator_entire R hRa n a ha.1) m

end ClassicalAllContourPeriodData

/-- One actual normalized moment family retains all-mode analyticity,
zeroth periods and odd cancellation; every positive moment also vanishes
on each collapsed actual high gap, including the diagonal numerator. -/
theorem exists_classicalHill_normalized_moments_with_collapsed_tail :
    ∃ N M : ℕ, ∃ U : Set (Curve ℂ),
      ∃ R : Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2),
        0 < N ∧ 0 < M ∧ IsOpen U ∧ 0 ∈ U ∧ AnalyticOnNhd ℂ R U ∧
        R 0 = ContinuousLinearMap.id ℂ (NLS.Coeff 2) ∧
        (∀ n k : ℕ+, ∀ m : ℕ, AnalyticOnNhd ℂ (classicalHillNormalizedMoment N R n k m) U) ∧
        (∀ a ∈ U, ∀ n k : ℕ+,
          (2*(Real.pi : ℂ))⁻¹*classicalHillNormalizedMoment N R n k 0 a = if n = k then 1 else 0) ∧
        (∀ a ∈ U, ∀ n k : ℕ+, ∀ l : ℕ, classicalHillNormalizedMoment N R n k (2*l+1) a = 0) ∧
        ∀ a ∈ U, ∀ n k : ℕ+, M ≤ (k : ℕ) → classicalHillHighSquaredGap a k = 0 → ∀ m : ℕ,
          classicalHillNormalizedMoment N R n k (m+1) a = 0 := by
  obtain ⟨N,V,T,R,hN,_,h0V,_,hRa,_,hR0,hinv,hentry,A,D⟩ := exists_classicalHill_analytic_period_inverse
  obtain ⟨Wo,hWoV,hWo,h0Wo,_,hodd⟩ := D.exists_normalized_all_odd_moments R hRa
  obtain ⟨M,Wc,hM,hWcV,hWc,h0Wc,hma,hclosed⟩ := D.exists_normalized_high_collapsed_moments R hRa 0 h0V
  let U := Wo ∩ Wc
  have hUV : U ⊆ V := fun _ ha => hWcV ha.2
  refine ⟨N,M,U,R,hN,hM,hWo.inter hWc,⟨h0Wo,h0Wc⟩,hRa.mono hUV,hR0,?_,?_,?_,?_⟩
  · intro n k m
    exact (hma n k m).mono inter_subset_right
  · intro a ha n k
    exact D.normalizedMoment_zero_order R T n k a (hUV ha) (hentry a (hUV ha)) (hinv a (hUV ha)).1
  · intro a ha n k l
    exact hodd a ha.1 n k l
  · intro a ha n k hk hgap m
    exact hclosed a ha.2 n k hk hgap m

end NLS.KdV
