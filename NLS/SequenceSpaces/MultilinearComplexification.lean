import NLS.SequenceSpaces.CoefficientComplexification
import Mathlib.Analysis.Normed.Module.Multilinear.Curry

/-! # Complexifying real multilinear coefficients

Repeated currying extends one variable at a time. The degree-n operator norm
increases by at most `2^n`, preserving positive radii of power-series convergence.
-/
noncomputable section
open scoped ENNReal
namespace NLS.Coeff.Complexification
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Extend all variables of a real multilinear coefficient to complex sequences. -/
def complexifyMultilinear : (n : ℕ) →
    (RealCoeff p [×n]→L[ℝ] F) →L[ℝ] (Coeff p [×n]→L[ℂ] F)
  | 0 =>
    (((continuousMultilinearCurryFin0 ℂ (Coeff p) F).symm.toContinuousLinearEquiv.toContinuousLinearMap).restrictScalars ℝ).comp
      (continuousMultilinearCurryFin0 ℝ (RealCoeff p) F).toContinuousLinearEquiv.toContinuousLinearMap
  | n+1 =>
    (((continuousMultilinearCurryLeftEquiv ℂ (fun _ : Fin (n+1) => Coeff p) F).symm.toContinuousLinearEquiv.toContinuousLinearMap).restrictScalars ℝ).comp
      (((complexifyCLM (p := p) (F := Coeff p [×n]→L[ℂ] F)).restrictScalars ℝ).comp
        ((ContinuousLinearMap.compL ℝ (RealCoeff p) (RealCoeff p [×n]→L[ℝ] F) (Coeff p [×n]→L[ℂ] F)
          (complexifyMultilinear n)).comp
            (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) => RealCoeff p) F).toContinuousLinearEquiv.toContinuousLinearMap))

@[simp] theorem complexifyMultilinear_zero (m : RealCoeff p [×0]→L[ℝ] F) :
    complexifyMultilinear 0 m = ContinuousMultilinearMap.uncurry0 ℂ (Coeff p) m.curry0 := rfl

/-- The recursive extension first complexifies the remaining variables, then the first. -/
theorem complexifyMultilinear_succ (n : ℕ) (m : RealCoeff p [×(n+1)]→L[ℝ] F) :
    complexifyMultilinear (n+1) m =
      (complexifyLinear ((complexifyMultilinear (p := p) (F := F) n).comp m.curryLeft)).uncurryLeft := rfl

/-- The coefficient norm grows at most exponentially in its degree. -/
theorem norm_complexifyMultilinear_apply_le (n : ℕ) (m : RealCoeff p [×n]→L[ℝ] F) :
    ‖complexifyMultilinear (p := p) (F := F) n m‖ ≤ 2^n*‖m‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [complexifyMultilinear_succ,ContinuousLinearMap.uncurryLeft_norm]
    have hn : ‖complexifyMultilinear (p := p) (F := F) n‖ ≤ 2^n :=
      ContinuousLinearMap.opNorm_le_bound _ (by positivity) ih
    calc
      ‖complexifyLinear ((complexifyMultilinear (p := p) (F := F) n).comp m.curryLeft)‖ ≤
          2*‖(complexifyMultilinear (p := p) (F := F) n).comp m.curryLeft‖ := norm_complexifyLinear_le _
      _ ≤ 2*(‖complexifyMultilinear (p := p) (F := F) n‖*‖m.curryLeft‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (by norm_num)
      _ ≤ 2*(2^n*‖m‖) := by rw [ContinuousMultilinearMap.curryLeft_norm]; gcongr
      _ = 2^(n+1)*‖m‖ := by rw [pow_succ]; ring

/-- Norm of the bounded coefficient-extension operator. -/
theorem norm_complexifyMultilinear_le (n : ℕ) :
    ‖complexifyMultilinear (p := p) (F := F) n‖ ≤ 2^n :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) (norm_complexifyMultilinear_apply_le n)

/-- Exact recovery on arbitrary tuples of real coefficient sequences. -/
@[simp] theorem complexifyMultilinear_real (n : ℕ) (m : RealCoeff p [×n]→L[ℝ] F)
    (v : Fin n → RealCoeff p) :
    complexifyMultilinear (p := p) (F := F) n m (fun i => RealCoeff.complexCLM p (v i)) = m v := by
  induction n with
  | zero =>
    simp only [complexifyMultilinear_zero,ContinuousMultilinearMap.uncurry0_apply,ContinuousMultilinearMap.curry0_apply]
    congr 1
    exact Subsingleton.elim _ _
  | succ n ih =>
    rw [complexifyMultilinear_succ,ContinuousLinearMap.uncurryLeft_apply,complexifyLinear_real,
      ContinuousLinearMap.comp_apply]
    change complexifyMultilinear (p := p) (F := F) n (m.curryLeft (v 0))
      (fun i => RealCoeff.complexCLM p (Fin.tail v i)) = _
    rw [ih,ContinuousMultilinearMap.curryLeft_apply,Fin.cons_self_tail]

end NLS.Coeff.Complexification
