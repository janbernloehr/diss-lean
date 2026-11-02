import NLS.KdV.ClassicalNormalizedProductConstant
import NLS.KdV.FrequencyMoments

/-! # Literal moments of the actual normalized Hill differentials

The source energy contour is the quadratic image of C(k*pi,pi/4).
Every integrand retains the actual shifted primitive, normalized entire
numerator, continued root and exact differential 2*z.
-/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
namespace NLS.KdV

def classicalHillNormalizedMomentIntegrand (N : ℕ)
    (R : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (n k : ℕ+) (m : ℕ) (t : ℂ × NLS.LinearVolterra.Curve ℂ) : ℂ :=
  (classicalHillFrequencyPrimitive t+I*(k : ℂ)*Real.pi)^m*
    (classicalHillNormalizedNumerator N R n (t.1^2,t.2)/classicalHillContinuedRoot (t.1^2,t.2))*(2*t.1)

def classicalHillNormalizedMoment (N : ℕ)
    (R : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (n k : ℕ+) (m : ℕ) (q : NLS.LinearVolterra.Curve ℂ) : ℂ :=
  ∮ z in C((Real.pi : ℂ)*(k : ℕ),Real.pi/4), classicalHillNormalizedMomentIntegrand N R n k m (z,q)

theorem classicalHillNormalizedMoment_eq_curveIntegral (N : ℕ)
    (R : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (n k : ℕ+) (m : ℕ) (q : NLS.LinearVolterra.Curve ℂ) :
    classicalHillNormalizedMoment N R n k m q =
      ∫ᶜ z in classicalHillHighEnergyContour k,
        holomorphicOneForm (fun z => (classicalHillContinuedPrimitive (z,q)+I*(k : ℂ)*Real.pi)^m*
          (classicalHillNormalizedNumerator N R n (z,q)/classicalHillContinuedRoot (z,q))) z := by
  let f : ℂ → ℂ := fun z => (classicalHillContinuedPrimitive (z,q)+I*(k : ℂ)*Real.pi)^m*
    (classicalHillNormalizedNumerator N R n (z,q)/classicalHillContinuedRoot (z,q))
  have hsq (z : ℂ) : HasDerivAt (fun w : ℂ => w^2) (2*z) z := by simpa using! (hasDerivAt_id z).pow 2
  have hp := (holomorphicPathPullback_integral_and_integrability f
    (fun z => f (z^2)*(2*z)) (fun z : ℂ => z^2) (fun z : ℂ => 2*z) (continuous_id.pow 2)
    (circlePath ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4))
    ((circlePath_contDiffOn _ _).of_le (by norm_num))
    (fun _ _ => hsq _) (fun _ _ => rfl)).2
  rw [curveIntegral_circlePath] at hp
  exact hp.symm

namespace ClassicalAllContourPeriodData
variable {N : ℕ} {V : Set (NLS.LinearVolterra.Curve ℂ)} {A : ℝ}
variable (D : ClassicalAllContourPeriodData N V A)
include D

theorem normalizedMomentIntegrand_analytic
    (R : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (hRa : AnalyticOnNhd ℂ R V) (n k : ℕ+) (m : ℕ) :
    AnalyticOnNhd ℂ (classicalHillNormalizedMomentIntegrand N R n k m)
      (classicalHillFrequencyDomain ∩ (univ ×ˢ V)) := by
  intro t ht
  have hF := analyticOnNhd_classicalHillFrequencyPrimitive t ht.1
  have hP := (D.normalizedNumerator_analytic R hRa n (t.1^2,t.2) ⟨mem_univ _,ht.2.2⟩).comp
    (f := fun t : ℂ × NLS.LinearVolterra.Curve ℂ => (t.1^2,t.2)) ((analyticAt_fst.pow 2).prod analyticAt_snd)
  have hroot := (analyticOnNhd_classicalHillContinuedRoot (t.1^2,t.2) ht.1).comp
    (f := fun t : ℂ × NLS.LinearVolterra.Curve ℂ => (t.1^2,t.2)) ((analyticAt_fst.pow 2).prod analyticAt_snd)
  exact ((hF.add analyticAt_const).pow m).mul
    (hP.div hroot (classicalHillContinuedRoot_ne_zero _ ht.1)) |>.mul (analyticAt_const.mul analyticAt_fst)

theorem normalizedMoment_analytic
    (R : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (hRa : AnalyticOnNhd ℂ R V) (n k : ℕ+) (m : ℕ) :
    AnalyticOnNhd ℂ (classicalHillNormalizedMoment N R n k m) V := by
  exact analyticOnNhd_circleIntegral_of_jointAnalytic (classicalHillNormalizedMomentIntegrand N R n k m)
    (isOpen_classicalHillFrequencyDomain.inter (isOpen_univ.prod D.isOpen))
    (D.normalizedMomentIntegrand_analytic R hRa n k m) ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4)
    (by positivity) D.isOpen (fun q hq z hz => ⟨D.cover k q hq z hz,mem_univ _,hq⟩)

theorem normalizedMoment_zero_order
    (R T : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (n k : ℕ+) (q : NLS.LinearVolterra.Curve ℂ) (hq : q ∈ V)
    (hentry : ∀ m j : ℤ, (T q (lp.single 2 j 1)) m = classicalHillPeriodMatrix N q m j)
    (hTR : (T q).comp (R q) = ContinuousLinearMap.id ℂ (NLS.Coeff 2)) :
    (2*(Real.pi : ℂ))⁻¹*classicalHillNormalizedMoment N R n k 0 q = if n = k then 1 else 0 := by
  simpa only [classicalHillNormalizedMoment,classicalHillNormalizedMomentIntegrand,pow_zero,one_mul] using!
    D.normalizedNumerator_period n k q hq T R hentry hTR

end ClassicalAllContourPeriodData
end NLS.KdV
