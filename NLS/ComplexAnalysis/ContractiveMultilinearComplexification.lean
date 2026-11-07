import NLS.ComplexAnalysis.ContractiveComplexification
import Mathlib.Analysis.Normed.Module.Multilinear.Curry

/-! # Complexifying real multilinear coefficients

Repeated currying extends one variable at a time. The degree-n operator norm
increases by at most `2^n`, preserving positive radii of power-series convergence.
-/
noncomputable section
open scoped ENNReal
namespace NLS.ComplexAnalysis.ContractiveComplexification
variable {R E : Type*} [NormedAddCommGroup R] [NormedSpace ℝ R]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
variable (c : ContractiveComplexification R E)
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Extend all variables of a real multilinear coefficient to complex sequences. -/
def complexifyMultilinear : (n : ℕ) →
    (R [×n]→L[ℝ] F) →L[ℝ] (E [×n]→L[ℂ] F)
  | 0 =>
    (((continuousMultilinearCurryFin0 ℂ (E) F).symm.toContinuousLinearEquiv.toContinuousLinearMap).restrictScalars ℝ).comp
      (continuousMultilinearCurryFin0 ℝ (R) F).toContinuousLinearEquiv.toContinuousLinearMap
  | n+1 =>
    (((continuousMultilinearCurryLeftEquiv ℂ (fun _ : Fin (n+1) => E) F).symm.toContinuousLinearEquiv.toContinuousLinearMap).restrictScalars ℝ).comp
      (((complexifyCLM (F := E [×n]→L[ℂ] F) c).restrictScalars ℝ).comp
        ((ContinuousLinearMap.compL ℝ (R) (R [×n]→L[ℝ] F) (E [×n]→L[ℂ] F)
          (complexifyMultilinear n)).comp
            (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) => R) F).toContinuousLinearEquiv.toContinuousLinearMap))

@[simp] theorem complexifyMultilinear_zero (m : R [×0]→L[ℝ] F) :
    complexifyMultilinear c 0 m = ContinuousMultilinearMap.uncurry0 ℂ (E) m.curry0 := rfl

/-- The recursive extension first complexifies the remaining variables, then the first. -/
theorem complexifyMultilinear_succ (n : ℕ) (m : R [×(n+1)]→L[ℝ] F) :
    complexifyMultilinear c (n+1) m =
      (complexifyLinear c ((complexifyMultilinear (F := F) c n).comp m.curryLeft)).uncurryLeft := rfl

/-- The coefficient norm grows at most exponentially in its degree. -/
theorem norm_complexifyMultilinear_apply_le (n : ℕ) (m : R [×n]→L[ℝ] F) :
    ‖complexifyMultilinear (F := F) c n m‖ ≤ 2^n*‖m‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [complexifyMultilinear_succ,ContinuousLinearMap.uncurryLeft_norm]
    have hn : ‖complexifyMultilinear (F := F) c n‖ ≤ 2^n :=
      ContinuousLinearMap.opNorm_le_bound _ (by positivity) ih
    calc
      ‖complexifyLinear c ((complexifyMultilinear (F := F) c n).comp m.curryLeft)‖ ≤
          2*‖(complexifyMultilinear (F := F) c n).comp m.curryLeft‖ := norm_complexifyLinear_le c _
      _ ≤ 2*(‖complexifyMultilinear (F := F) c n‖*‖m.curryLeft‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (by norm_num)
      _ ≤ 2*(2^n*‖m‖) := by rw [ContinuousMultilinearMap.curryLeft_norm]; gcongr
      _ = 2^(n+1)*‖m‖ := by rw [pow_succ]; ring

/-- Norm of the bounded coefficient-extension operator. -/
theorem norm_complexifyMultilinear_le (n : ℕ) :
    ‖complexifyMultilinear (F := F) c n‖ ≤ 2^n :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) (norm_complexifyMultilinear_apply_le c n)

/-- Exact recovery on arbitrary tuples of real coefficient sequences. -/
@[simp] theorem complexifyMultilinear_real (n : ℕ) (m : R [×n]→L[ℝ] F)
    (v : Fin n → R) :
    complexifyMultilinear (F := F) c n m (fun i => c.inclusion (v i)) = m v := by
  induction n with
  | zero =>
    simp only [complexifyMultilinear_zero,ContinuousMultilinearMap.uncurry0_apply,ContinuousMultilinearMap.curry0_apply]
    congr 1
    exact Subsingleton.elim _ _
  | succ n ih =>
    rw [complexifyMultilinear_succ,ContinuousLinearMap.uncurryLeft_apply,complexifyLinear_real,
      ContinuousLinearMap.comp_apply]
    change complexifyMultilinear (F := F) c n (m.curryLeft (v 0))
      (fun i => c.inclusion (Fin.tail v i)) = _
    rw [ih,ContinuousMultilinearMap.curryLeft_apply,Fin.cons_self_tail]

end NLS.ComplexAnalysis.ContractiveComplexification
