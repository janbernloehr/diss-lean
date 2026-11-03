import NLS.KdV.HillHminusOneTwoWeightedPeriodInverse
import NLS.SequenceSpaces.AnalyticTwoWeightedInverseColumns
import NLS.KdV.ClassicalRoughNormalizationCompatibility
import NLS.KdV.ClassicalNormalizedOddMoments
import NLS.ComplexAnalysis.DenseLinearAnalyticUniqueness

/-! # Actual rough normalized moments with twice-weighted inverse columns

The weighted inverse, exact periods and every odd cancellation belong to
one constructed family on one rough-open neighborhood before all indices.
-/
noncomputable section
open Set Metric Complex Filter Topology NLS.LinearVolterra NLS.ComplexAnalysis
namespace NLS.KdV
namespace HillHminusUniformPeriodData
variable {C : HillHminusMiuraChart} {N : ℕ} {V : Set PeriodOneHminusOne} {A : ℝ}
variable (D : HillHminusUniformPeriodData C N V A)
include D

/-- Cancellation applies to any actual analytic inverse, including the
constructed weighted-compatible one. -/
theorem exists_all_odd_moments_of_inverse
    (T R : PeriodOneHminusOne → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (hRa : AnalyticOnNhd ℂ R V)
    (hentry : ∀ q ∈ V, ∀ m n : ℤ, (T q (lp.single 2 n 1)) m = hillHminusPeriodMatrix C N q m n)
    (hRT : ∀ q ∈ V, (R q).comp (T q) = ContinuousLinearMap.id ℂ (NLS.Coeff 2)) :
    ∃ U : Set PeriodOneHminusOne, U ⊆ V ∧ IsOpen U ∧ 0 ∈ U ∧
      ∀ q ∈ U, ∀ n k : ℕ+, ∀ l : ℕ, hillHminusNormalizedMoment C N R n k (2*l+1) q = 0 := by
  obtain ⟨M,W,Tc,Rc,_,_,_,_,hRca,_,_,hinvc,hentryc,B,Dc⟩ := exists_classicalHill_analytic_period_inverse
  obtain ⟨Uo,_,hUo,h0Uo,_,hodd⟩ := Dc.exists_normalized_all_odd_moments Rc hRca
  obtain ⟨Uc,hUcW,hUcV,hUc,h0Uc,hcrit⟩ := D.exists_critical_compatibility Dc
  have hCompat (q : Curve ℂ) (hq : q ∈ Uc) (n k : ℕ+) (m : ℕ) :
      hillHminusNormalizedMoment C N R n k m (classicalHillHminusInclusion q) =
        classicalHillNormalizedMoment M Rc n k m q := by
    have hR := inverse_eq_classical Dc q (hUcW hq) (fun j => hcrit j q hq)
      (T (classicalHillHminusInclusion q)) (R (classicalHillHminusInclusion q)) (Tc q) (Rc q)
      (hentry _ (hUcV hq)) (hentryc q (hUcW hq)) (hRT _ (hUcV hq)) (hinvc q (hUcW hq)).1
    exact D.normalizedMoment_eq_classical Dc R Rc q (hUcV hq) (hUcW hq)
      (fun j => hcrit j q hq) hR n k m
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (D.isOpen.mem_nhds D.zero_mem)
  refine ⟨ball 0 r,hball,isOpen_ball,mem_ball_self hr,?_⟩
  intro q hq n k l
  have hnear : (fun a => hillHminusNormalizedMoment C N R n k (2*l+1) (classicalHillHminusInclusion a))
      =ᶠ[𝓝 (0 : Curve ℂ)] 0 := by
    filter_upwards [(hUc.inter hUo).mem_nhds ⟨h0Uc,h0Uo⟩] with a ha
    exact (hCompat a ha.1 n k (2*l+1)).trans (hodd a ha.2 n k l)
  exact eqOn_zero_of_dense_linear_pullback classicalHillHminusInclusion denseRange_classicalHillHminusInclusion
    (ball 0 r) isOpen_ball (convex_ball 0 r) (mem_ball_self hr)
    (hillHminusNormalizedMoment C N R n k (2*l+1)) ((D.normalizedMoment_analytic R hRa n k _).mono hball) hnear hq

end HillHminusUniformPeriodData

structure HillHminusTwoWeightedNormalizedMomentData (C : HillHminusMiuraChart) (N : ℕ)
    (V : Set PeriodOneHminusOne)
    (T R S Q : PeriodOneHminusOne → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2)) : Prop where
  source_data : ∃ A : ℝ, HillHminusUniformPeriodData C N V A
  analytic_T : AnalyticOnNhd ℂ T V
  analytic_R : AnalyticOnNhd ℂ R V
  analytic_S : AnalyticOnNhd ℂ S V
  analytic_Q : AnalyticOnNhd ℂ Q V
  free_T : T 0 = ContinuousLinearMap.id ℂ (NLS.Coeff 2)
  free_R : R 0 = ContinuousLinearMap.id ℂ (NLS.Coeff 2)
  free_S : S 0 = ContinuousLinearMap.id ℂ (NLS.Coeff 2)
  free_Q : Q 0 = ContinuousLinearMap.id ℂ (NLS.Coeff 2)
  inverses : ∀ q ∈ V, (T q).comp (R q) = ContinuousLinearMap.id ℂ (NLS.Coeff 2) ∧
    (R q).comp (T q) = ContinuousLinearMap.id ℂ (NLS.Coeff 2) ∧
    (S q).comp (Q q) = ContinuousLinearMap.id ℂ (NLS.Coeff 2) ∧
    (Q q).comp (S q) = ContinuousLinearMap.id ℂ (NLS.Coeff 2) ∧ ‖R q‖ ≤ 2 ∧ ‖Q q‖ ≤ 2
  entries : ∀ q ∈ V, ∀ m n : ℤ,
    (T q (lp.single 2 n 1)) m = hillHminusPeriodMatrix C N q m n ∧
    (S q (lp.single 2 n 1)) m = hillHminusTwoWeightedPeriodMatrix C N q m n
  compatibility : ∀ q ∈ V, ∀ m n : ℤ,
    NLS.Coeff.positiveIndexWeight m^2*(R q (lp.single 2 n 1)) m =
      NLS.Coeff.positiveIndexWeight n^2*(Q q (lp.single 2 n 1)) m
  weighted_error_analytic : ∀ n : ℕ+, AnalyticOnNhd ℂ (NLS.Coeff.twoWeightedInverseError Q n) V
  weighted_error_memlp : ∀ q ∈ V, ∀ n : ℕ+, Memℓp (fun m : ℤ =>
    NLS.Coeff.positiveIndexWeight m^2*((R q (lp.single 2 (n : ℤ) 1)) m-
      (lp.single 2 (n : ℤ) (1 : ℂ) : NLS.Coeff 2) m)) 2
  numerator_analytic : ∀ n : ℕ+, AnalyticOnNhd ℂ (hillHminusNormalizedNumerator C N R n) (univ ×ˢ V)
  numerator_free : ∀ n : ℕ+, ∀ z : ℂ, hillHminusNormalizedNumerator C N R n (z,0) = classicalHillFreePsi n z
  moment_analytic : ∀ n k : ℕ+, ∀ m : ℕ, AnalyticOnNhd ℂ (hillHminusNormalizedMoment C N R n k m) V
  moment_zero : ∀ q ∈ V, ∀ n k : ℕ+,
    (2*(Real.pi : ℂ))⁻¹*hillHminusNormalizedMoment C N R n k 0 q = if n = k then 1 else 0
  moment_odd : ∀ q ∈ V, ∀ n k : ℕ+, ∀ l : ℕ, hillHminusNormalizedMoment C N R n k (2*l+1) q = 0

theorem exists_hillHminus_twoWeighted_normalized_moments :
    ∃ C : HillHminusMiuraChart, ∃ N : ℕ, ∃ V : Set PeriodOneHminusOne,
      ∃ T R S Q : PeriodOneHminusOne → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2),
        0 < N ∧ IsOpen V ∧ 0 ∈ V ∧ HillHminusTwoWeightedNormalizedMomentData C N V T R S Q := by
  obtain ⟨C,N,W,T,R,S,Q,hN,_,_,hTa,hRa,hSa,hQa,hT0,hR0,hS0,hQ0,hinv,hentry,hcompat,A,D⟩ :=
    exists_hillHminus_twoWeighted_period_inverse
  obtain ⟨V,hVW,hV,h0V,hodd⟩ := D.exists_all_odd_moments_of_inverse T R hRa
    (fun q hq m n => (hentry q hq m n).1) (fun q hq => (hinv q hq).2.1)
  have Dr := D.mono hVW hV h0V
  refine ⟨C,N,V,T,R,S,Q,hN,hV,h0V,{
    source_data := ⟨A,Dr⟩
    analytic_T := hTa.mono hVW
    analytic_R := hRa.mono hVW
    analytic_S := hSa.mono hVW
    analytic_Q := hQa.mono hVW
    free_T := hT0, free_R := hR0, free_S := hS0, free_Q := hQ0
    inverses := fun q hq => hinv q (hVW hq)
    entries := fun q hq m n => hentry q (hVW hq) m n
    compatibility := fun q hq m n => hcompat q (hVW hq) m n
    weighted_error_analytic := fun n => NLS.Coeff.twoWeightedInverseError_analytic Q V (hQa.mono hVW) n
    weighted_error_memlp := fun q hq n => NLS.Coeff.twoWeightedInverseError_memlp R Q q (hcompat q (hVW hq)) n
    numerator_analytic := Dr.normalizedNumerator_analytic R (hRa.mono hVW)
    numerator_free := Dr.normalizedNumerator_free R hR0
    moment_analytic := Dr.normalizedMoment_analytic R (hRa.mono hVW)
    moment_zero := fun q hq n k => Dr.normalizedMoment_zero_order R T n k q hq
      (fun m j => (hentry q (hVW hq) m j).1) (hinv q (hVW hq)).1
    moment_odd := hodd }⟩

end NLS.KdV
