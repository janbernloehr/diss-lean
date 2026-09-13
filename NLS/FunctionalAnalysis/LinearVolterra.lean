import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Topology.ContinuousMap.Algebra

/-!
# Linear Volterra equations on the unit interval

A continuous operator coefficient admits a unique integral solution on the
whole unit interval. Factorial decay makes an iterate of the Picard map
contracting, without a smallness condition on the coefficient.
-/

noncomputable section
open Set Function Filter Topology MeasureTheory intervalIntegral
open scoped Nat NNReal
namespace NLS.LinearVolterra
variable {E : Type*} [NormedAddCommGroup E]

/-- Continuous curves on the closed unit interval. -/
abbrev Curve (E : Type*) [TopologicalSpace E] := C(Icc (0 : ℝ) 1, E)

/-- Constant extension beyond the endpoints. -/
def extend (u : Curve E) (t : ℝ) : E := u (projIcc 0 1 (by norm_num) t)

@[simp] theorem extend_coe (u : Curve E) (t : Icc (0 : ℝ) 1) : extend u t = u t := by
  simp [extend]

theorem continuous_extend (u : Curve E) : Continuous (extend u) :=
  u.continuous.comp continuous_projIcc

variable [NormedSpace ℝ E]

/-- The Volterra integrand with the coefficient and curve extended continuously. -/
def integrand (A : Curve (E →L[ℝ] E)) (u : Curve E) (t : ℝ) : E :=
  extend A t (extend u t)

theorem continuous_integrand (A : Curve (E →L[ℝ] E)) (u : Curve E) :
    Continuous (integrand A u) := (continuous_extend A).clm_apply (continuous_extend u)

variable [CompleteSpace E]

/-- One Picard step on the full continuous-curve Banach space. -/
def next (A : Curve (E →L[ℝ] E)) (x : E) (u : Curve E) : Curve E where
  toFun t := x + ∫ s in (0 : ℝ)..t.val, integrand A u s
  continuous_toFun := continuous_const.add
    ((intervalIntegral.differentiable_integral_of_continuous (continuous_integrand A u)).continuous.comp
      continuous_subtype_val)

@[simp] theorem next_apply (A : Curve (E →L[ℝ] E)) (x : E) (u : Curve E) (t : Icc (0 : ℝ) 1) :
    next A x u t = x + ∫ s in (0 : ℝ)..t.val, integrand A u s := rfl

/-- Pointwise factorial estimate for arbitrary Picard iterates and starting curves. -/
theorem dist_iterate_next_apply_le (A : Curve (E →L[ℝ] E)) (x : E)
    (K : ℝ≥0) (hK : ∀ t, ‖A t‖ ≤ K) (u v : Curve E) (n : ℕ) (t : Icc (0 : ℝ) 1) :
    dist ((next A x)^[n] u t) ((next A x)^[n] v t) ≤
      (K * t.val)^n / n.factorial * dist u v := by
  induction n generalizing t with
  | zero => simpa using ContinuousMap.dist_apply_le_dist t (f := u) (g := v)
  | succ n ih =>
    rw [iterate_succ_apply',iterate_succ_apply',dist_eq_norm,next_apply,next_apply,
      add_sub_add_left_eq_sub, ← intervalIntegral.integral_sub
        ((continuous_integrand A _).intervalIntegrable _ _)
        ((continuous_integrand A _).intervalIntegrable _ _)]
    calc
      _ ≤ ∫ s in (0 : ℝ)..t.val, (K : ℝ)^(n+1) * s^n / n.factorial * dist u v := by
        apply intervalIntegral.norm_integral_le_of_norm_le t.property.1
        · apply Filter.Eventually.of_forall
          intro s hs
          have hs' : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1.le,hs.2.trans t.property.2⟩
          simp only [integrand,extend,projIcc_of_mem _ hs']
          rw [← map_sub]
          calc
            _ ≤ ‖A ⟨s,hs'⟩‖ * ‖((next A x)^[n] u) ⟨s,hs'⟩ - ((next A x)^[n] v) ⟨s,hs'⟩‖ :=
              ContinuousLinearMap.le_opNorm _ _
            _ ≤ (K : ℝ) * ((K * s)^n / n.factorial * dist u v) := by
              gcongr
              · exact hK _
              · simpa only [dist_eq_norm] using ih ⟨s,hs'⟩
            _ = _ := by rw [mul_pow,pow_succ]; ring
        · exact Continuous.intervalIntegrable (by fun_prop) _ _
      _ = (K * t.val)^(n+1) / (n+1).factorial * dist u v := by
        rw [intervalIntegral.integral_mul_const,intervalIntegral.integral_div,
          intervalIntegral.integral_const_mul,integral_pow]
        simp only [zero_pow (Nat.succ_ne_zero n),sub_zero,Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,mul_pow]
        field_simp

/-- A uniform factorial bound for the Picard iterates in the supremum metric. -/
theorem dist_iterate_next_le (A : Curve (E →L[ℝ] E)) (x : E)
    (K : ℝ≥0) (hK : ∀ t, ‖A t‖ ≤ K) (u v : Curve E) (n : ℕ) :
    dist ((next A x)^[n] u) ((next A x)^[n] v) ≤ (K : ℝ)^n / n.factorial * dist u v := by
  apply (ContinuousMap.dist_le (by positivity)).mpr
  intro t
  apply (dist_iterate_next_apply_le A x K hK u v n t).trans
  gcongr
  · exact mul_nonneg K.coe_nonneg t.property.1
  · exact mul_le_of_le_one_right K.coe_nonneg t.property.2

/-- Every continuous linear coefficient has a contracting Picard iterate. -/
theorem exists_contracting_iterate (A : Curve (E →L[ℝ] E)) (x : E) :
    ∃ n : ℕ, ∃ K : ℝ≥0, ContractingWith K (next A x)^[n] := by
  obtain ⟨n,hn⟩ := (FloorSemiring.tendsto_pow_div_factorial_atTop ‖A‖).eventually
    (gt_mem_nhds zero_lt_one) |>.exists
  refine ⟨n,⟨‖A‖^n / n.factorial,by positivity⟩,hn,?_⟩
  exact LipschitzWith.of_dist_le_mul (fun u v =>
    dist_iterate_next_le A x ‖A‖₊ (fun t => A.norm_coe_le_norm t) u v n)

/-- The Volterra equation has a unique continuous solution for every initial value. -/
theorem existsUnique_solution (A : Curve (E →L[ℝ] E)) (x : E) :
    ∃! u : Curve E, ∀ t, u t = x + ∫ s in (0 : ℝ)..t.val, integrand A u s := by
  obtain ⟨n,K,h⟩ := exists_contracting_iterate A x
  refine ⟨h.fixedPoint _,?_,?_⟩
  · intro t
    exact (congrArg (fun u : Curve E => u t) h.isFixedPt_fixedPoint_iterate).symm
  · intro u hu
    have hf : IsFixedPt (next A x) u := by ext t; exact (hu t).symm
    exact h.fixedPoint_unique (hf.iterate n)

end NLS.LinearVolterra
