import NLS.FunctionalAnalysis.LinearVolterraSolution
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Algebra.Group.Commute.Units

/-!
# The complex Volterra operator and its inverse

Integration against a continuous complex-linear coefficient defines a bounded
operator on continuous curves. Its powers satisfy a factorial norm bound, so
one minus this operator is invertible for every coefficient size.
-/

noncomputable section
open Set Filter Topology Function MeasureTheory intervalIntegral
open scoped NNReal
namespace NLS.LinearVolterra
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- Restrict the coefficient scalars for the real-time integral equation. -/
def realCoefficient (A : Curve (E →L[ℂ] E)) : Curve (E →L[ℝ] E) where
  toFun t := (A t).restrictScalars ℝ
  continuous_toFun := by fun_prop

/-- The zero-initial-value Picard map is bounded by the coefficient supremum norm. -/
theorem norm_next_zero_le (A : Curve (E →L[ℂ] E)) (u : Curve E) :
    ‖next (realCoefficient A) 0 u‖ ≤ ‖A‖ * ‖u‖ := by
  have hz : next (realCoefficient A) 0 (0 : Curve E) = 0 := by
    ext t
    simp [next,integrand,extend]
  have h := dist_iterate_next_le (realCoefficient A) 0 ‖A‖₊
    (fun t => by simpa only [realCoefficient,ContinuousMap.coe_mk,ContinuousLinearMap.norm_restrictScalars,coe_nnnorm] using! A.norm_coe_le_norm t) u 0 1
  simpa only [iterate_one,hz,dist_zero_right,pow_one,Nat.factorial_one,Nat.cast_one,div_one,coe_nnnorm] using! h

/-- The bounded Volterra operator on complex continuous curves. -/
def volterra (A : Curve (E →L[ℂ] E)) : Curve E →L[ℂ] Curve E :=
  LinearMap.mkContinuous
    { toFun := next (realCoefficient A) 0
      map_add' := by
        intro u v
        ext t
        simp only [next_apply,zero_add,ContinuousMap.add_apply]
        change (∫ s in (0 : ℝ)..t.val, extend A s (extend (u+v) s)) =
          (∫ s in (0 : ℝ)..t.val, extend A s (extend u s)) +
          (∫ s in (0 : ℝ)..t.val, extend A s (extend v s))
        simp only [extend,ContinuousMap.add_apply,map_add]
        exact intervalIntegral.integral_add
          ((continuous_integrand (realCoefficient A) u).intervalIntegrable _ _)
          ((continuous_integrand (realCoefficient A) v).intervalIntegrable _ _)
      map_smul' := by
        intro c u
        ext t
        simp only [next_apply,zero_add,ContinuousMap.smul_apply,RingHom.id_apply]
        change (∫ s in (0 : ℝ)..t.val, extend A s (extend (c • u) s)) =
          c • (∫ s in (0 : ℝ)..t.val, extend A s (extend u s))
        simp only [extend,ContinuousMap.smul_apply,map_smul]
        exact intervalIntegral.integral_smul _ _ }
    ‖A‖ (norm_next_zero_le A)

@[simp] theorem volterra_apply (A : Curve (E →L[ℂ] E)) (u : Curve E) (t : Icc (0 : ℝ) 1) :
    volterra A u t = ∫ s in (0 : ℝ)..t.val, extend A s (extend u s) := by
  change (0 : E) + _ = _
  rw [zero_add]
  rfl

/-- The Volterra operator norm is bounded by the coefficient norm. -/
theorem norm_volterra_le (A : Curve (E →L[ℂ] E)) : ‖volterra A‖ ≤ ‖A‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg A) _

/-- Operator powers are the zero-initial-value Picard iterates. -/
theorem volterra_pow_apply (A : Curve (E →L[ℂ] E)) (n : ℕ) (u : Curve E) :
    (volterra A ^ n) u = (next (realCoefficient A) 0)^[n] u := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ',mul_apply_eq_comp,ih,iterate_succ_apply']
    rfl

/-- The Volterra powers decay factorially in operator norm. -/
theorem norm_volterra_pow_le (A : Curve (E →L[ℂ] E)) (n : ℕ) :
    ‖volterra A ^ n‖ ≤ ‖A‖^n / n.factorial := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  have h := dist_iterate_next_le (realCoefficient A) 0 ‖A‖₊
    (fun t => by simpa only [realCoefficient,ContinuousMap.coe_mk,ContinuousLinearMap.norm_restrictScalars,coe_nnnorm] using! A.norm_coe_le_norm t) u 0 n
  rw [← volterra_pow_apply,← volterra_pow_apply,map_zero,dist_zero_right,dist_zero_right] at h
  exact h

/-- The Volterra equation is globally invertible, without a small coefficient assumption. -/
theorem isUnit_one_sub_volterra (A : Curve (E →L[ℂ] E)) : IsUnit (1-volterra A) := by
  obtain ⟨n,hn⟩ := (FloorSemiring.tendsto_pow_div_factorial_atTop ‖A‖).eventually
    (gt_mem_nhds zero_lt_one) |>.exists
  have hn' : ‖volterra A ^ n‖ < 1 := (norm_volterra_pow_le A n).trans_lt hn
  have hu : IsUnit (1-volterra A ^ n) := isUnit_one_sub_of_norm_lt_one (R := Curve E →L[ℂ] Curve E) hn'
  have hc : Commute (1-volterra A) (∑ i ∈ Finset.range n, volterra A ^ i) := by
    change _ * _ = _ * _
    rw [mul_neg_geom_sum,geom_sum_mul_neg]
  exact (hc.isUnit_mul_iff.mp (by rwa [mul_neg_geom_sum])).1

end NLS.LinearVolterra
