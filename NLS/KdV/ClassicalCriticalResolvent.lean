import NLS.KdV.ClassicalSignedCriticalProduct
import NLS.KdV.ClassicalAllContourPeriodBounds

/-! # Actual analytic Hilbert critical resolvents

The entire numerator basis, divided by the actual discriminant derivative,
constructs the resolvent off the critical set. Its negative energy derivative
is a genuine Hilbert vector with the literal squared-denominator coordinates.
Completeness of the selected critical labels proves that every original
positive frequency circle lies in this domain, including the finite head.
-/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV

def classicalHillCriticalResolventDomain (V : Set (NLS.LinearVolterra.Curve ℂ)) :
    Set (ℂ × NLS.LinearVolterra.Curve ℂ) :=
  (univ ×ˢ V) ∩ {t | classicalHillDiscriminantDerivative t ≠ 0}

def classicalHillCriticalResolvent (N : ℕ) (t : ℂ × NLS.LinearVolterra.Curve ℂ) : NLS.Coeff 2 :=
  (2*(Real.pi : ℂ)*classicalHillDiscriminantDerivative t)⁻¹ • classicalHillNumeratorHilbert N t

def classicalHillSquaredCriticalResolvent (N : ℕ) (q : NLS.LinearVolterra.Curve ℂ)
    (z : ℂ) : NLS.Coeff 2 :=
  -deriv (fun w => classicalHillCriticalResolvent N (w,q)) z

namespace ClassicalAllContourPeriodData
variable {N : ℕ} {V : Set (NLS.LinearVolterra.Curve ℂ)} {A : ℝ}
variable (D : ClassicalAllContourPeriodData N V A)
include D

theorem critical_sub_ne_zero_on_contour (j k : ℕ+) (q : NLS.LinearVolterra.Curve ℂ)
    (hq : q ∈ V) (z : ℂ) (hz : z ∈ sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4)) :
    z^2-classicalHillUniformCriticalPoint N j q ≠ 0 := by
  by_cases he : j = k
  · subst j
    exact norm_pos_iff.mp ((by positivity : 0 < Real.pi^2/8*(k : ℝ)).trans_le
      (D.diagonal_separation k q hq z hz))
  have hd : 0 < |(k : ℝ)^2-(j : ℝ)^2| := by
    apply abs_pos.mpr
    rw [sq_sub_sq]
    apply mul_ne_zero (by positivity)
    exact sub_ne_zero.mpr (by exact_mod_cast Ne.symm he)
  exact norm_pos_iff.mp ((mul_pos (by positivity : 0 < Real.pi^2/4) hd).trans_le
    (D.offDiagonal_separation j k he q hq z hz))

theorem discriminant_derivative_ne_zero_on_contour (k : ℕ+) (q : NLS.LinearVolterra.Curve ℂ)
    (hq : q ∈ V) (z : ℂ) (hz : z ∈ sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4)) :
    deriv (classicalHillDiscriminant q) (z^2) ≠ 0 := by
  intro he
  obtain ⟨M,hlabel⟩ := (D.signedCritical_product q hq).1
  have hfreq : deriv (canonicalDiscriminant (by simp) (classicalHillCoefficientPotential q)) z = 0 := by
    rw [classicalHill_frequency_derivative_eq,he,mul_zero]
  obtain ⟨j,hj⟩ := (hlabel.exhaustive z).mp hfreq
  have hsq := congrArg (fun w : ℂ => w^2) hj
  by_cases hjpos : 0 < j
  · rw [classicalHillSignedCritical,dif_pos hjpos,sq_sqrt] at hsq
    exact D.critical_sub_ne_zero_on_contour (positiveIntegerIndex j hjpos) k q hq z hz
      (sub_eq_zero.mpr hsq.symm)
  by_cases hjneg : j < 0
  · rw [classicalHillSignedCritical,dif_neg hjpos,dif_pos hjneg,neg_sq,sq_sqrt] at hsq
    exact D.critical_sub_ne_zero_on_contour (positiveIntegerIndex (-j) (by omega)) k q hq z hz
      (sub_eq_zero.mpr hsq.symm)
  have hjzero : j = 0 := by omega
  rw [hjzero,classicalHillSignedCritical_zero] at hj
  have hp := re_pos_of_high_closedBall _ k.property z (sphere_subset_closedBall hz)
  simp only [← hj,zero_re,lt_self_iff_false] at hp

theorem criticalResolventDomain_isOpen : IsOpen (classicalHillCriticalResolventDomain V) :=
  (isOpen_univ.prod D.isOpen).inter
    (isOpen_ne_fun analyticOnNhd_classicalHillDiscriminantDerivative.continuous continuous_const)

theorem criticalResolvent_analytic :
    AnalyticOnNhd ℂ (classicalHillCriticalResolvent N) (classicalHillCriticalResolventDomain V) := by
  intro t ht
  exact ((analyticAt_const.mul (analyticOnNhd_classicalHillDiscriminantDerivative t (mem_univ _))).inv
    (mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) ht.2)).smul
      (D.numeratorHilbert_spec.2 t ht.1)

theorem criticalResolvent_positive (q : NLS.LinearVolterra.Curve ℂ) (hq : q ∈ V)
    (z : ℂ) (hne : deriv (classicalHillDiscriminant q) z ≠ 0) (j : ℕ+) :
    classicalHillCriticalResolvent N (z,q) (j : ℤ) =
      (j : ℂ)/(z-classicalHillUniformCriticalPoint N j q) := by
  have hd : z-classicalHillUniformCriticalPoint N j q ≠ 0 := by
    intro he
    exact hne (sub_eq_zero.mp he ▸ D.critical_zero j q hq)
  have hf := D.numerator_factor j q hq z
  have hb : classicalHillUniformNumerator N j (z,q) =
      (2*(j : ℂ)*Real.pi)*deriv (classicalHillDiscriminant q) z/
        (z-classicalHillUniformCriticalPoint N j q) := (eq_div_iff hd).mpr ((mul_comm _ _).trans hf)
  simp only [classicalHillCriticalResolvent,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,
    D.numeratorHilbert_positive (z,q) ⟨mem_univ _,hq⟩,hb,classicalHillDiscriminantDerivative]
  field_simp

theorem criticalResolvent_nonpositive (q : NLS.LinearVolterra.Curve ℂ) (hq : q ∈ V)
    (z : ℂ) (j : ℤ) (hj : j ≤ 0) : classicalHillCriticalResolvent N (z,q) j = 0 := by
  simp only [classicalHillCriticalResolvent,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,
    D.numeratorHilbert_spec.1 (z,q) ⟨mem_univ _,hq⟩,classicalHillNumeratorCoordinates,
    dif_neg (by omega : ¬ 0 < j),mul_zero]

theorem squaredCriticalResolvent_positive (q : NLS.LinearVolterra.Curve ℂ) (hq : q ∈ V)
    (z : ℂ) (hne : deriv (classicalHillDiscriminant q) z ≠ 0) (j : ℕ+) :
    classicalHillSquaredCriticalResolvent N q z (j : ℤ) =
      (j : ℂ)/(z-classicalHillUniformCriticalPoint N j q)^2 := by
  have hR : AnalyticAt ℂ (fun w => classicalHillCriticalResolvent N (w,q)) z :=
    (D.criticalResolvent_analytic (z,q) ⟨⟨mem_univ _,hq⟩,hne⟩).comp
      (f := fun w : ℂ => (w,q)) (analyticAt_id.prod analyticAt_const)
  have hd : z-classicalHillUniformCriticalPoint N j q ≠ 0 := by
    intro he
    exact hne (sub_eq_zero.mp he ▸ D.critical_zero j q hq)
  have hnear : (fun w => classicalHillCriticalResolvent N (w,q) (j : ℤ)) =ᶠ[𝓝 z]
      (fun w => (j : ℂ)/(w-classicalHillUniformCriticalPoint N j q)) := by
    have hc := ((analyticOnNhd_classicalHillDiscriminant q).deriv z (mem_univ _)).continuousAt
    filter_upwards [hc.eventually_ne hne] with w hw
    exact D.criticalResolvent_positive q hq w hw j
  have hscalar := (hasDerivAt_const z (j : ℂ)).div ((hasDerivAt_id z).sub_const _) hd
  have hev := (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 (j : ℤ)).hasFDerivAt.comp_hasDerivAt z hR.differentiableAt.hasDerivAt
  have hev' : deriv (fun w => classicalHillCriticalResolvent N (w,q) (j : ℤ)) z =
      (deriv (fun w => classicalHillCriticalResolvent N (w,q)) z) (j : ℤ) := hev.deriv
  have he := hev'.symm.trans (hnear.deriv_eq.trans hscalar.deriv)
  simp only [classicalHillSquaredCriticalResolvent,lp.coeFn_neg,Pi.neg_apply,he]
  simp [neg_div]

theorem squaredCriticalResolvent_nonpositive (q : NLS.LinearVolterra.Curve ℂ) (hq : q ∈ V)
    (z : ℂ) (hne : deriv (classicalHillDiscriminant q) z ≠ 0) (j : ℤ) (hj : j ≤ 0) :
    classicalHillSquaredCriticalResolvent N q z j = 0 := by
  have hR : AnalyticAt ℂ (fun w => classicalHillCriticalResolvent N (w,q)) z :=
    (D.criticalResolvent_analytic (z,q) ⟨⟨mem_univ _,hq⟩,hne⟩).comp
      (f := fun w : ℂ => (w,q)) (analyticAt_id.prod analyticAt_const)
  have hev := (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 j).hasFDerivAt.comp_hasDerivAt z hR.differentiableAt.hasDerivAt
  have heq : (fun w => classicalHillCriticalResolvent N (w,q) j) = fun _ => (0 : ℂ) :=
    funext (fun w => D.criticalResolvent_nonpositive q hq w j hj)
  have he : deriv (fun w => classicalHillCriticalResolvent N (w,q) j) z =
      (deriv (fun w => classicalHillCriticalResolvent N (w,q)) z) j := hev.deriv
  rw [heq,deriv_const] at he
  simp only [classicalHillSquaredCriticalResolvent,lp.coeFn_neg,Pi.neg_apply,← he,neg_zero]

theorem squaredCriticalResolvent_analytic (q : NLS.LinearVolterra.Curve ℂ) (hq : q ∈ V) :
    AnalyticOnNhd ℂ (classicalHillSquaredCriticalResolvent N q)
      {z | deriv (classicalHillDiscriminant q) z ≠ 0} := by
  have hR : AnalyticOnNhd ℂ (fun z => classicalHillCriticalResolvent N (z,q))
      {z | deriv (classicalHillDiscriminant q) z ≠ 0} := by
    intro z hz
    exact (D.criticalResolvent_analytic (z,q) ⟨⟨mem_univ _,hq⟩,hz⟩).comp
      (f := fun w : ℂ => (w,q)) (analyticAt_id.prod analyticAt_const)
  exact hR.deriv.neg

end ClassicalAllContourPeriodData
end NLS.KdV
