import NLS.KdV.ClassicalDiscriminant
import NLS.FunctionalAnalysis.LinearVolterraRegularity
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# The scalar Hill state flow and its weak uniqueness

The state is the actual scalar position and derivative. The direct
Volterra realization is identified with the shared constant-upper
construction, so its trace is the same entire Hill discriminant.
Absolutely continuous scalar weak solutions have exactly this state flow.
-/

noncomputable section
open Set Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.FunctionalAnalysis NLS.ZakharovShabat
namespace NLS.KdV

/-- The literal scalar state equation `(F,G)'=(G,(q-lambda)*F)`. -/
def classicalHillCoefficient (q lambda : ℂ) : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) :=
  (ContinuousLinearMap.snd ℂ ℂ ℂ).prod
    ((q-lambda) • ContinuousLinearMap.fst ℂ ℂ ℂ)

@[simp] theorem classicalHillCoefficient_apply (q lambda : ℂ) (v : ℂ × ℂ) :
    classicalHillCoefficient q lambda v = (v.2,(q-lambda)*v.1) := rfl

def classicalHillCoefficientCurve (q : Curve ℂ) (lambda : ℂ) :
    Curve ((ℂ × ℂ) →L[ℝ] (ℂ × ℂ)) where
  toFun t := (classicalHillCoefficient (q t) lambda).restrictScalars ℝ
  continuous_toFun := by
    have hc : Continuous (fun t => classicalHillCoefficient (q t) lambda) := by
      exact (ContinuousLinearMap.prodₗᵢ ℂ).continuous.comp
        (show Continuous (fun t => (ContinuousLinearMap.snd ℂ ℂ ℂ,
          (q t-lambda) • ContinuousLinearMap.fst ℂ ℂ ℂ)) by fun_prop)
    fun_prop

/-- The actual scalar position/derivative IVP with arbitrary initial state. -/
def classicalHillFlow (q : Curve ℂ) (lambda : ℂ) (v : ℂ × ℂ) : ℝ → ℂ × ℂ :=
  solution (classicalHillCoefficientCurve q lambda) v

@[simp] theorem classicalHillFlow_zero (q : Curve ℂ) (lambda : ℂ) (v : ℂ × ℂ) :
    classicalHillFlow q lambda v 0 = v := solution_zero _ _

theorem hasDerivAt_classicalHillFlow (q : Curve ℂ) (lambda : ℂ) (v : ℂ × ℂ)
    (t : Icc (0 : ℝ) 1) :
    HasDerivAt (classicalHillFlow q lambda v)
      ((classicalHillFlow q lambda v t).2,(q t-lambda)*(classicalHillFlow q lambda v t).1) t :=
  hasDerivAt_solution_coe _ _ t

theorem classicalHillCoefficient_stateMap (q z : ℂ) (v : ℂ × ℂ) :
    classicalHillCoefficient q (z^2) (constantUpperStateMap z v) =
      constantUpperStateMap z (classicalODECoefficient (-1,-q) z v) := by
  apply Prod.ext <;>
    simp only [classicalHillCoefficient_apply, constantUpperStateMap_apply, classicalODECoefficient_apply]
  · ring
  · ring_nf
    simp [I_sq]
    ring

/-- The direct scalar IVP is exactly the already constructed normalized
scalar solution, with no restriction at the zero energy. -/
theorem classicalHillFlow_eq_constantUpper (q : Curve ℂ) (z : ℂ) (v : ℂ × ℂ)
    (t : Icc (0 : ℝ) 1) :
    classicalHillFlow q (z^2) v t = constantUpperStateMap z
      (classicalSolution (constantUpperPotential q) z (constantUpperInitialVector z v) t) := by
  apply Eq.symm
  apply solution_unique (classicalHillCoefficientCurve q (z^2)) v
    (fun x => constantUpperStateMap z
      (classicalSolution (constantUpperPotential q) z (constantUpperInitialVector z v) x))
    ((constantUpperStateMap z).continuous.comp (continuous_classicalSolution _ _ _)).continuousOn
    (by rw [classicalSolution_zero, constantUpperStateMap_initialVector]) _ t.property
  intro s _
  have hd := ((constantUpperStateMap z).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (s : ℝ)
    (hasDerivAt_classicalSolution (constantUpperPotential q) z (constantUpperInitialVector z v) s)
  change HasDerivAt _ (classicalHillCoefficient (q s) (z^2)
    (constantUpperStateMap z (classicalSolution (constantUpperPotential q) z
      (constantUpperInitialVector z v) s))) (s : ℝ)
  rw [classicalHillCoefficient_stateMap, ← constantUpperPotential_apply q s]
  exact hd

/-- The trace of the scalar flow has the exact shared Hill normalization. -/
theorem classicalHillFlow_trace (q : Curve ℂ) (lambda : ℂ) :
    (classicalHillFlow q lambda (1,0) 1).1+(classicalHillFlow q lambda (0,1) 1).2 =
      classicalHillDiscriminant q lambda := by
  obtain ⟨z, rfl⟩ := IsAlgClosed.exists_pow_nat_eq lambda (by norm_num : 0 < 2)
  have ht : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by constructor <;> norm_num
  rw [classicalHillFlow_eq_constantUpper q z (1,0) ⟨1,ht⟩,
    classicalHillFlow_eq_constantUpper q z (0,1) ⟨1,ht⟩,
    classicalHillDiscriminant_eq_scalar_trace q (z^2) z rfl]
  unfold constantUpperHillTrace
  rw [constantUpperHillState_eq q z _ ⟨1,ht⟩, constantUpperHillState_eq q z _ ⟨1,ht⟩]

/-- Weak scalar solutions with an AC derivative representative are the
actual scalar IVP solution with the same initial position and derivative. -/
theorem classicalHillFlow_unique_of_ac (q : Curve ℂ) (lambda : ℂ) (F G : ℝ → ℂ)
    (hF : AbsolutelyContinuousOnInterval F 0 1) (hG : AbsolutelyContinuousOnInterval G 0 1)
    (hFG : ∀ᵐ x : ℝ, x ∈ Icc (0 : ℝ) 1 → deriv F x = G x)
    (hEq : ∀ᵐ x : ℝ, x ∈ Icc (0 : ℝ) 1 →
      deriv G x = (extend q x-lambda)*F x) :
    EqOn (fun x => (F x,G x)) (classicalHillFlow q lambda (F 0,G 0)) (Icc 0 1) := by
  have h1 := absolutelyContinuousOnInterval_clm hF (ContinuousLinearMap.inl ℝ ℂ ℂ)
  have h2 := absolutelyContinuousOnInterval_clm hG (ContinuousLinearMap.inr ℝ ℂ ℂ)
  have hstate : AbsolutelyContinuousOnInterval (fun x => (F x,G x)) 0 1 := by
    apply absolutelyContinuousOnInterval_congr (h1.add h2)
    intro x _
    simp only [Pi.add_apply, ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply,
      Prod.add_def, add_zero, zero_add]
  apply solution_unique_of_ac (classicalHillCoefficientCurve q lambda) _ hstate
  filter_upwards [ae_differentiableAt_complex hF, ae_differentiableAt_complex hG, hFG, hEq] with x hxF hxG hxFG hxEq
  intro hxi
  have hxu : x ∈ uIcc (0 : ℝ) 1 := by
    rwa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have hd := (hxF hxu).hasDerivAt.prodMk (hxG hxu).hasDerivAt
  rw [hxFG hxi, hxEq hxi] at hd
  simpa only [LinearVolterra.extend, projIcc_of_mem _ hxi, classicalHillCoefficientCurve,
    ContinuousMap.coe_mk, ContinuousLinearMap.coe_restrictScalars', classicalHillCoefficient_apply] using hd

end NLS.KdV
