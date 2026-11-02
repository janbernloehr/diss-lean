import NLS.KdV.ClassicalNormalizedCollapsedMoments
import NLS.KdV.ClassicalCriticalResolvent
import NLS.ComplexAnalysis.CirclePowerIntegrationByParts

/-! # Exact squared-resolvent formulas for actual normalized moments

The constructed Hilbert resolvent and closed-circle integration by parts
raise the primitive power by one and square every critical denominator.
A genuine Hilbert-valued Bochner integral justifies the absolutely
convergent positive-index expansion outside the contour integral.
-/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
namespace NLS.KdV

def classicalHillMomentResolventVector (N : ℕ) (k : ℕ+) (m : ℕ)
    (q : NLS.LinearVolterra.Curve ℂ) : NLS.Coeff 2 :=
  ∮ z in C((Real.pi : ℂ)*(k : ℕ),Real.pi/4),
    ((classicalHillContinuedPrimitive (z^2,q)+I*(k : ℂ)*Real.pi)^(m+1)*(2*z)) •
      classicalHillSquaredCriticalResolvent N q (z^2)

namespace ClassicalAllContourPeriodData
variable {N : ℕ} {V : Set (NLS.LinearVolterra.Curve ℂ)} {A : ℝ}
variable (D : ClassicalAllContourPeriodData N V A)
include D

theorem momentResolvent_contour_integrable (k : ℕ+) (m : ℕ)
    (q : NLS.LinearVolterra.Curve ℂ) (hq : q ∈ V) :
    CircleIntegrable (fun z : ℂ =>
      ((classicalHillContinuedPrimitive (z^2,q)+I*(k : ℂ)*Real.pi)^(m+1)*(2*z)) •
        classicalHillSquaredCriticalResolvent N q (z^2))
      ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4) := by
  have hf : AnalyticOnNhd ℂ (fun z => classicalHillContinuedPrimitive (z^2,q)+I*(k : ℂ)*Real.pi)
      (sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4)) := by
    intro z hz
    exact ((analyticOnNhd_classicalHillContinuedPrimitive (z^2,q) (D.cover k q hq z hz)).comp
      (f := fun z : ℂ => (z^2,q)) ((analyticAt_id.pow 2).prod analyticAt_const)).add analyticAt_const
  have hw : AnalyticOnNhd ℂ (fun z => classicalHillSquaredCriticalResolvent N q (z^2))
      (sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4)) := by
    intro z hz
    exact (D.squaredCriticalResolvent_analytic q hq (z^2)
      (D.discriminant_derivative_ne_zero_on_contour k q hq z hz)).comp
        (f := fun z : ℂ => z^2) (analyticAt_id.pow 2)
  exact ((((hf.pow (m+1)).mul (analyticOnNhd_const.mul analyticOnNhd_id)).smul hw).continuousOn).circleIntegrable (by positivity)

theorem momentResolventVector_positive (k j : ℕ+) (m : ℕ)
    (q : NLS.LinearVolterra.Curve ℂ) (hq : q ∈ V) :
    classicalHillMomentResolventVector N k m q (j : ℤ) = (j : ℂ)*
      ∮ z in C((Real.pi : ℂ)*(k : ℕ),Real.pi/4),
        (classicalHillContinuedPrimitive (z^2,q)+I*(k : ℂ)*Real.pi)^(m+1)*(2*z)/
          (z^2-classicalHillUniformCriticalPoint N j q)^2 := by
  change (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 (j : ℤ)) (classicalHillMomentResolventVector N k m q) = _
  unfold classicalHillMomentResolventVector
  rw [map_circleIntegral _ (D.momentResolvent_contour_integrable k m q hq),← circleIntegral.integral_const_mul]
  apply circleIntegral.integral_congr (by positivity)
  intro z hz
  simp only [map_smul,smul_eq_mul]
  change ((classicalHillContinuedPrimitive (z^2,q)+I*(k : ℂ)*Real.pi)^(m+1)*(2*z))*
    classicalHillSquaredCriticalResolvent N q (z^2) (j : ℤ) = _
  rw [D.squaredCriticalResolvent_positive q hq (z^2) (D.discriminant_derivative_ne_zero_on_contour k q hq z hz) j]
  ring

theorem momentResolventVector_nonpositive (k : ℕ+) (m : ℕ)
    (q : NLS.LinearVolterra.Curve ℂ) (hq : q ∈ V) (j : ℤ) (hj : j ≤ 0) :
    classicalHillMomentResolventVector N k m q j = 0 := by
  change (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 j) (classicalHillMomentResolventVector N k m q) = _
  unfold classicalHillMomentResolventVector
  rw [map_circleIntegral _ (D.momentResolvent_contour_integrable k m q hq)]
  have heq : (∮ z in C((Real.pi : ℂ)*(k : ℕ),Real.pi/4),
      (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 j)
        (((classicalHillContinuedPrimitive (z^2,q)+I*(k : ℂ)*Real.pi)^(m+1)*(2*z)) •
          classicalHillSquaredCriticalResolvent N q (z^2))) =
      (∮ z in C((Real.pi : ℂ)*(k : ℕ),Real.pi/4), (0 : ℂ)) := by
    apply circleIntegral.integral_congr (by positivity)
    intro z hz
    simp only [map_smul,smul_eq_mul]
    change ((classicalHillContinuedPrimitive (z^2,q)+I*(k : ℂ)*Real.pi)^(m+1)*(2*z))*
      classicalHillSquaredCriticalResolvent N q (z^2) j = 0
    rw [D.squaredCriticalResolvent_nonpositive q hq (z^2) (D.discriminant_derivative_ne_zero_on_contour k q hq z hz) j hj,mul_zero]
  rw [heq]
  simp only [circleIntegral,smul_zero,intervalIntegral.integral_zero]

theorem momentResolventVector_positive_series (k : ℕ+) (m : ℕ)
    (q : NLS.LinearVolterra.Curve ℂ) (hq : q ∈ V) (c : NLS.Coeff 2) :
    Summable (fun j : ℕ+ => ‖(j : ℂ)*c (j : ℤ)*
      ∮ z in C((Real.pi : ℂ)*(k : ℕ),Real.pi/4),
        (classicalHillContinuedPrimitive (z^2,q)+I*(k : ℂ)*Real.pi)^(m+1)*(2*z)/
          (z^2-classicalHillUniformCriticalPoint N j q)^2‖) ∧
    NLS.Coeff.dualPairing c (classicalHillMomentResolventVector N k m q) =
      ∑' j : ℕ+, (j : ℂ)*c (j : ℤ)*
        ∮ z in C((Real.pi : ℂ)*(k : ℕ),Real.pi/4),
          (classicalHillContinuedPrimitive (z^2,q)+I*(k : ℂ)*Real.pi)^(m+1)*(2*z)/
            (z^2-classicalHillUniformCriticalPoint N j q)^2 := by
  have hi : Function.Injective (fun j : ℕ+ => (j : ℤ)) := by
    intro i j hij
    apply Subtype.ext
    exact Int.ofNat_inj.mp hij
  have he (j : ℕ+) : c (j : ℤ)*classicalHillMomentResolventVector N k m q (j : ℤ) =
      (j : ℂ)*c (j : ℤ)*(∮ z in C((Real.pi : ℂ)*(k : ℕ),Real.pi/4),
        (classicalHillContinuedPrimitive (z^2,q)+I*(k : ℂ)*Real.pi)^(m+1)*(2*z)/
          (z^2-classicalHillUniformCriticalPoint N j q)^2) := by
    rw [D.momentResolventVector_positive k j m q hq]
    ring
  constructor
  · simpa only [Function.comp_def,he] using!
      (NLS.Coeff.summable_norm_dualPairing c (classicalHillMomentResolventVector N k m q)).comp_injective hi
  rw [NLS.Coeff.dualPairing_apply,tsum_eq_positive_of_nonpositive_zero _
    (fun j hj => by rw [D.momentResolventVector_nonpositive k m q hq j hj,mul_zero])]
  exact tsum_congr he

theorem normalizedMoment_eq_resolvent_vector
    (R : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (n k : ℕ+) (m : ℕ) (q : NLS.LinearVolterra.Curve ℂ) (hq : q ∈ V) :
    classicalHillNormalizedMoment N R n k m q = (2*(Real.pi : ℂ))/(m+1)*
      NLS.Coeff.dualPairing (R q (lp.single 2 (n : ℤ) 1)) (classicalHillMomentResolventVector N k m q) := by
  let F (z : ℂ) := classicalHillContinuedPrimitive (z^2,q)+I*(k : ℂ)*Real.pi
  let L : NLS.Coeff 2 →L[ℂ] ℂ := NLS.Coeff.dualPairing (R q (lp.single 2 (n : ℤ) 1))
  let G (z : ℂ) := L (classicalHillCriticalResolvent N (z^2,q))
  let c : ℂ := (Real.pi : ℂ)*(k : ℕ)
  have hF : AnalyticOnNhd ℂ F (sphere c (Real.pi/4)) := by
    intro z hz
    exact ((analyticOnNhd_classicalHillContinuedPrimitive (z^2,q) (D.cover k q hq z hz)).comp
      (f := fun z : ℂ => (z^2,q)) ((analyticAt_id.pow 2).prod analyticAt_const)).add analyticAt_const
  have hG : AnalyticOnNhd ℂ G (sphere c (Real.pi/4)) := by
    intro z hz
    exact L.analyticAt _ |>.comp (f := fun z : ℂ => classicalHillCriticalResolvent N (z^2,q))
      ((D.criticalResolvent_analytic (z^2,q) ⟨⟨mem_univ _,hq⟩,D.discriminant_derivative_ne_zero_on_contour k q hq z hz⟩).comp
        (f := fun z : ℂ => (z^2,q)) ((analyticAt_id.pow 2).prod analyticAt_const))
  have hDF (z : ℂ) (hz : z ∈ sphere c (Real.pi/4)) :
      deriv F z = (deriv (classicalHillDiscriminant q) (z^2)/classicalHillContinuedRoot (z^2,q))*(2*z) := by
    have hsq : HasDerivAt (fun w : ℂ => w^2) (2*z) z := by simpa using! (hasDerivAt_id z).pow 2
    exact ((hasDerivAt_classicalHillContinuedPrimitive (z^2,q) (D.cover k q hq z hz)).comp z hsq |>.add_const _).deriv
  have hDG (z : ℂ) (hz : z ∈ sphere c (Real.pi/4)) :
      deriv G z = -(L (classicalHillSquaredCriticalResolvent N q (z^2)))*(2*z) := by
    have hR : AnalyticAt ℂ (fun w => classicalHillCriticalResolvent N (w,q)) (z^2) :=
      (D.criticalResolvent_analytic (z^2,q) ⟨⟨mem_univ _,hq⟩,D.discriminant_derivative_ne_zero_on_contour k q hq z hz⟩).comp
        (f := fun w : ℂ => (w,q)) (analyticAt_id.prod analyticAt_const)
    have hsq : HasDerivAt (fun w : ℂ => w^2) (2*z) z := by simpa using! (hasDerivAt_id z).pow 2
    have hd := L.hasFDerivAt.comp_hasDerivAt z (hR.differentiableAt.hasDerivAt.scomp z hsq)
    have hd' : HasDerivAt G (L ((2*z) • deriv (fun w => classicalHillCriticalResolvent N (w,q)) (z^2))) z := hd
    rw [hd'.deriv]
    simp only [classicalHillSquaredCriticalResolvent,map_neg,map_smul,smul_eq_mul]
    ring
  have hp (z : ℂ) (hz : z ∈ sphere c (Real.pi/4)) :
      F z^m*deriv F z*G z = (2*(Real.pi : ℂ))⁻¹*classicalHillNormalizedMomentIntegrand N R n k m (z,q) := by
    rw [hDF z hz]
    dsimp only [G,classicalHillCriticalResolvent]
    rw [map_smul]
    change _ = (2*(Real.pi : ℂ))⁻¹*(F z^m*(L (classicalHillNumeratorHilbert N (z^2,q))/classicalHillContinuedRoot (z^2,q))*(2*z))
    have hne := D.discriminant_derivative_ne_zero_on_contour k q hq z hz
    change deriv (classicalHillDiscriminant q) (z^2) ≠ 0 at hne
    simp only [smul_eq_mul,classicalHillDiscriminantDerivative]
    field_simp [hne,classicalHillContinuedRoot_ne_zero _ (D.cover k q hq z hz)]
  have hmap : L (classicalHillMomentResolventVector N k m q) =
      ∮ z in C(c,Real.pi/4), F z^(m+1)*L (classicalHillSquaredCriticalResolvent N q (z^2))*(2*z) := by
    change L (∮ z in C(c,Real.pi/4), _) = _
    rw [map_circleIntegral L (D.momentResolvent_contour_integrable k m q hq)]
    apply circleIntegral.integral_congr (by positivity)
    intro z _
    simp only [map_smul,smul_eq_mul]
    ring
  have hsecond : (∮ z in C(c,Real.pi/4), F z^(m+1)*deriv G z) =
      -(L (classicalHillMomentResolventVector N k m q)) := by
    rw [hmap,← neg_one_mul,← circleIntegral.integral_const_mul]
    apply circleIntegral.integral_congr (by positivity)
    intro z hz
    change F z^(m+1)*deriv G z = (-1 : ℂ)*(F z^(m+1)*L (classicalHillSquaredCriticalResolvent N q (z^2))*(2*z))
    rw [hDG z hz]
    ring
  have hi := circleIntegral_power_mul_deriv F G c (Real.pi/4) (by positivity) hF hG m
  rw [circleIntegral.integral_congr (by positivity) hp,circleIntegral.integral_const_mul,hsecond] at hi
  change (2*(Real.pi : ℂ))⁻¹*classicalHillNormalizedMoment N R n k m q = _ at hi
  calc
    _ = (2*(Real.pi : ℂ))*((2*(Real.pi : ℂ))⁻¹*classicalHillNormalizedMoment N R n k m q) := by field_simp
    _ = _ := by rw [hi];ring

/-- Literal absolutely convergent positive-index formula. No unproved
interchange of a scalar infinite sum and the contour integral is used. -/
theorem normalizedMoment_resolvent_series
    (R : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (n k : ℕ+) (m : ℕ) (q : NLS.LinearVolterra.Curve ℂ) (hq : q ∈ V) :
    Summable (fun j : ℕ+ => ‖(j : ℂ)*(R q (lp.single 2 (n : ℤ) 1)) (j : ℤ)*
      ∮ z in C((Real.pi : ℂ)*(k : ℕ),Real.pi/4),
        (classicalHillContinuedPrimitive (z^2,q)+I*(k : ℂ)*Real.pi)^(m+1)*(2*z)/
          (z^2-classicalHillUniformCriticalPoint N j q)^2‖) ∧
    classicalHillNormalizedMoment N R n k m q = (2*(Real.pi : ℂ))/(m+1)*
      ∑' j : ℕ+, (j : ℂ)*(R q (lp.single 2 (n : ℤ) 1)) (j : ℤ)*
        ∮ z in C((Real.pi : ℂ)*(k : ℕ),Real.pi/4),
          (classicalHillContinuedPrimitive (z^2,q)+I*(k : ℂ)*Real.pi)^(m+1)*(2*z)/
            (z^2-classicalHillUniformCriticalPoint N j q)^2 := by
  obtain ⟨hs,he⟩ := D.momentResolventVector_positive_series k m q hq (R q (lp.single 2 (n : ℤ) 1))
  exact ⟨hs,(D.normalizedMoment_eq_resolvent_vector R n k m q hq).trans (congrArg _ he)⟩

end ClassicalAllContourPeriodData

/-- The actual normalized family and all its squared-resolvent moment
formulas are constructed on one neighborhood before every positive
numerator index, contour index and moment order. -/
theorem exists_classicalHill_normalized_resolvent_moments :
    ∃ N : ℕ, ∃ U : Set (NLS.LinearVolterra.Curve ℂ),
      ∃ R : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2),
        0 < N ∧ IsOpen U ∧ 0 ∈ U ∧ AnalyticOnNhd ℂ R U ∧
        R 0 = ContinuousLinearMap.id ℂ (NLS.Coeff 2) ∧ (∀ q ∈ U, ‖R q‖ ≤ 2) ∧
        (∀ n k : ℕ+, ∀ m : ℕ, AnalyticOnNhd ℂ (classicalHillNormalizedMoment N R n k m) U) ∧
        (∀ q ∈ U, ∀ n k : ℕ+,
          (2*(Real.pi : ℂ))⁻¹*classicalHillNormalizedMoment N R n k 0 q = if n = k then 1 else 0) ∧
        (∀ q ∈ U, ∀ n k : ℕ+, ∀ l : ℕ, classicalHillNormalizedMoment N R n k (2*l+1) q = 0) ∧
        ∀ q ∈ U, ∀ n k : ℕ+, ∀ m : ℕ,
          Summable (fun j : ℕ+ => ‖(j : ℂ)*(R q (lp.single 2 (n : ℤ) 1)) (j : ℤ)*
            ∮ z in C((Real.pi : ℂ)*(k : ℕ),Real.pi/4),
              (classicalHillContinuedPrimitive (z^2,q)+I*(k : ℂ)*Real.pi)^(m+1)*(2*z)/
                (z^2-classicalHillUniformCriticalPoint N j q)^2‖) ∧
          classicalHillNormalizedMoment N R n k m q = (2*(Real.pi : ℂ))/(m+1)*
            ∑' j : ℕ+, (j : ℂ)*(R q (lp.single 2 (n : ℤ) 1)) (j : ℤ)*
              ∮ z in C((Real.pi : ℂ)*(k : ℕ),Real.pi/4),
                (classicalHillContinuedPrimitive (z^2,q)+I*(k : ℂ)*Real.pi)^(m+1)*(2*z)/
                  (z^2-classicalHillUniformCriticalPoint N j q)^2 := by
  obtain ⟨N,V,T,R,hN,_,_,_,hRa,_,hR0,hinv,hentry,A,D⟩ := exists_classicalHill_analytic_period_inverse
  obtain ⟨U,hUV,hU,h0U,hma,hodd⟩ := D.exists_normalized_all_odd_moments R hRa
  refine ⟨N,U,R,hN,hU,h0U,hRa.mono hUV,hR0,fun q hq => (hinv q (hUV hq)).2.2,
    hma,?_,hodd,?_⟩
  · intro q hq n k
    exact D.normalizedMoment_zero_order R T n k q (hUV hq) (hentry q (hUV hq)) (hinv q (hUV hq)).1
  intro q hq n k m
  exact D.normalizedMoment_resolvent_series R n k m q (hUV hq)

end NLS.KdV
