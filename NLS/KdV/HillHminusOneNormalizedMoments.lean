import NLS.KdV.HillHminusOneNormalizedDifferentials
import NLS.KdV.FrequencyMoments

/-! # Literal moments of the actual normalized Hill differentials

The source energy contour is the quadratic image of C(k*pi,pi/4).
Every integrand retains the actual shifted primitive, normalized entire
numerator, continued root and exact differential 2*z.
-/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
namespace NLS.KdV

def hillHminusFrequencyDomain : Set (ℂ × PeriodOneHminusOne) :=
  (fun t : ℂ × PeriodOneHminusOne => (t.1^2,t.2)) ⁻¹' hillHminusContinuationDomain

def hillHminusFrequencyPrimitive (t : ℂ × PeriodOneHminusOne) : ℂ :=
  hillHminusContinuedPrimitive (t.1^2,t.2)

theorem isOpen_hillHminusFrequencyDomain : IsOpen hillHminusFrequencyDomain :=
  isOpen_hillHminusContinuationDomain.preimage ((continuous_fst.pow 2).prodMk continuous_snd)

theorem analyticOnNhd_hillHminusFrequencyPrimitive :
    AnalyticOnNhd ℂ hillHminusFrequencyPrimitive hillHminusFrequencyDomain := by
  intro t ht
  exact (analyticOnNhd_hillHminusContinuedPrimitive (t.1^2,t.2) ht).comp
    (f := fun s : ℂ × PeriodOneHminusOne => (s.1^2,s.2)) ((analyticAt_fst.pow 2).prod analyticAt_snd)

def hillHminusNormalizedMomentIntegrand (C : HillHminusMiuraChart) (N : ℕ)
    (R : PeriodOneHminusOne → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (n k : ℕ+) (m : ℕ) (t : ℂ × PeriodOneHminusOne) : ℂ :=
  (hillHminusFrequencyPrimitive t+I*(k : ℂ)*Real.pi)^m*
    (hillHminusNormalizedNumerator C N R n (t.1^2,t.2)/hillHminusContinuedRoot (t.1^2,t.2))*(2*t.1)

def hillHminusNormalizedMoment (C : HillHminusMiuraChart) (N : ℕ)
    (R : PeriodOneHminusOne → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (n k : ℕ+) (m : ℕ) (q : PeriodOneHminusOne) : ℂ :=
  ∮ z in C((Real.pi : ℂ)*(k : ℕ),Real.pi/4), hillHminusNormalizedMomentIntegrand C N R n k m (z,q)

theorem hillHminusNormalizedMoment_eq_curveIntegral (C : HillHminusMiuraChart) (N : ℕ)
    (R : PeriodOneHminusOne → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (n k : ℕ+) (m : ℕ) (q : PeriodOneHminusOne) :
    hillHminusNormalizedMoment C N R n k m q =
      ∫ᶜ z in classicalHillHighEnergyContour k,
        holomorphicOneForm (fun z => (hillHminusContinuedPrimitive (z,q)+I*(k : ℂ)*Real.pi)^m*
          (hillHminusNormalizedNumerator C N R n (z,q)/hillHminusContinuedRoot (z,q))) z := by
  let f : ℂ → ℂ := fun z => (hillHminusContinuedPrimitive (z,q)+I*(k : ℂ)*Real.pi)^m*
    (hillHminusNormalizedNumerator C N R n (z,q)/hillHminusContinuedRoot (z,q))
  have hsq (z : ℂ) : HasDerivAt (fun w : ℂ => w^2) (2*z) z := by simpa using! (hasDerivAt_id z).pow 2
  have hp := (holomorphicPathPullback_integral_and_integrability f
    (fun z => f (z^2)*(2*z)) (fun z : ℂ => z^2) (fun z : ℂ => 2*z) (continuous_id.pow 2)
    (circlePath ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4))
    ((circlePath_contDiffOn _ _).of_le (by norm_num))
    (fun _ _ => hsq _) (fun _ _ => rfl)).2
  rw [curveIntegral_circlePath] at hp
  exact hp.symm

namespace HillHminusUniformPeriodData
variable {C : HillHminusMiuraChart} {N : ℕ} {V : Set (PeriodOneHminusOne)} {A : ℝ}
variable (D : HillHminusUniformPeriodData C N V A)
include D

theorem normalizedMomentIntegrand_analytic
    (R : PeriodOneHminusOne → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (hRa : AnalyticOnNhd ℂ R V) (n k : ℕ+) (m : ℕ) :
    AnalyticOnNhd ℂ (hillHminusNormalizedMomentIntegrand C N R n k m)
      (hillHminusFrequencyDomain ∩ (univ ×ˢ V)) := by
  intro t ht
  have hF := analyticOnNhd_hillHminusFrequencyPrimitive t ht.1
  have hP := (D.normalizedNumerator_analytic R hRa n (t.1^2,t.2) ⟨mem_univ _,ht.2.2⟩).comp
    (f := fun t : ℂ × PeriodOneHminusOne => (t.1^2,t.2)) ((analyticAt_fst.pow 2).prod analyticAt_snd)
  have hroot := (analyticOnNhd_hillHminusContinuedRoot (t.1^2,t.2) ht.1).comp
    (f := fun t : ℂ × PeriodOneHminusOne => (t.1^2,t.2)) ((analyticAt_fst.pow 2).prod analyticAt_snd)
  exact ((hF.add analyticAt_const).pow m).mul
    (hP.div hroot (hillHminusSourceFamily.root_ne_zero _ ht.1)) |>.mul (analyticAt_const.mul analyticAt_fst)

theorem normalizedMoment_analytic
    (R : PeriodOneHminusOne → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (hRa : AnalyticOnNhd ℂ R V) (n k : ℕ+) (m : ℕ) :
    AnalyticOnNhd ℂ (hillHminusNormalizedMoment C N R n k m) V := by
  exact analyticOnNhd_circleIntegral_of_jointAnalytic (hillHminusNormalizedMomentIntegrand C N R n k m)
    (isOpen_hillHminusFrequencyDomain.inter (isOpen_univ.prod D.isOpen))
    (D.normalizedMomentIntegrand_analytic R hRa n k m) ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4)
    (by positivity) D.isOpen (fun q hq z hz => ⟨D.cover k q hq z hz,mem_univ _,hq⟩)

theorem normalizedMoment_zero_order
    (R T : PeriodOneHminusOne → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (n k : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ V)
    (hentry : ∀ m j : ℤ, (T q (lp.single 2 j 1)) m = hillHminusPeriodMatrix C N q m j)
    (hTR : (T q).comp (R q) = ContinuousLinearMap.id ℂ (NLS.Coeff 2)) :
    (2*(Real.pi : ℂ))⁻¹*hillHminusNormalizedMoment C N R n k 0 q = if n = k then 1 else 0 := by
  simpa only [hillHminusNormalizedMoment,hillHminusNormalizedMomentIntegrand,pow_zero,one_mul] using!
    D.normalizedNumerator_period n k q hq T R hentry hTR

end HillHminusUniformPeriodData
/-- One actual rough-open source neighborhood precedes every numerator,
contour and moment order. This is a local moment construction near zero. -/
theorem exists_hillHminus_analytic_normalized_moments :
    ∃ C : HillHminusMiuraChart, ∃ N : ℕ, ∃ V : Set PeriodOneHminusOne,
      ∃ R : PeriodOneHminusOne → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2),
        0 < N ∧ IsOpen V ∧ 0 ∈ V ∧ AnalyticOnNhd ℂ R V ∧
        R 0 = ContinuousLinearMap.id ℂ (NLS.Coeff 2) ∧ (∀ q ∈ V, ‖R q‖ ≤ 2) ∧
        (∀ n : ℕ+, AnalyticOnNhd ℂ (hillHminusNormalizedNumerator C N R n) (univ ×ˢ V)) ∧
        (∀ n : ℕ+, ∀ z : ℂ, hillHminusNormalizedNumerator C N R n (z,0) = classicalHillFreePsi n z) ∧
        (∀ n k : ℕ+, ∀ m : ℕ, AnalyticOnNhd ℂ (hillHminusNormalizedMoment C N R n k m) V) ∧
        (∀ n k : ℕ+, ∀ q ∈ V,
          (2*(Real.pi : ℂ))⁻¹*hillHminusNormalizedMoment C N R n k 0 q = if n = k then 1 else 0) ∧
        ∃ A : ℝ, HillHminusUniformPeriodData C N V A := by
  obtain ⟨C,N,V,R,hN,hV,h0V,hRa,hR0,hRn,hPsi,hFree,hPeriods,A,D⟩ :=
    exists_hillHminus_infinite_normalized_differentials
  refine ⟨C,N,V,R,hN,hV,h0V,hRa,hR0,hRn,hPsi,hFree,
    D.normalizedMoment_analytic R hRa,?_,A,D⟩
  intro n k q hq
  simpa only [hillHminusNormalizedMoment,hillHminusNormalizedMomentIntegrand,pow_zero,one_mul]
    using hPeriods n k q hq

end NLS.KdV
