import NLS.FunctionalAnalysis.LinearVolterraSolution
import NLS.ZakharovShabat.PhysicalOperator
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Classical fundamental solutions and monodromy

For every continuous potential on the unit interval, construct solutions of
the actual Zakharov–Shabat differential equation. The two normalized columns
have constant Wronskian one, hence their endpoint monodromy is unimodular.
This construction does not yet identify its trace with the spectral products.
-/

noncomputable section
open Set Complex MeasureTheory intervalIntegral
open NLS.LinearVolterra
namespace NLS.ZakharovShabat

/-- The first-order system equivalent to the original spectral equation. -/
def classicalODECoefficient (φ : ℂ × ℂ) (z : ℂ) : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) :=
  ((-I*z) • ContinuousLinearMap.fst ℂ ℂ ℂ + (I*φ.1) • ContinuousLinearMap.snd ℂ ℂ ℂ).prod
    ((-I*φ.2) • ContinuousLinearMap.fst ℂ ℂ ℂ + (I*z) • ContinuousLinearMap.snd ℂ ℂ ℂ)

@[simp] theorem classicalODECoefficient_apply (φ : ℂ × ℂ) (z : ℂ) (y : ℂ × ℂ) :
    classicalODECoefficient φ z y = (-I*z*y.1+I*φ.1*y.2,-I*φ.2*y.1+I*z*y.2) := rfl

/-- The continuous real-linear coefficient used by the Volterra construction. -/
def classicalODECurve (φ : Curve (ℂ × ℂ)) (z : ℂ) : Curve ((ℂ × ℂ) →L[ℝ] (ℂ × ℂ)) where
  toFun t := (classicalODECoefficient (φ t) z).restrictScalars ℝ
  continuous_toFun := by
    have hc : Continuous (fun t => classicalODECoefficient (φ t) z) := by
      exact (ContinuousLinearMap.prodₗᵢ ℂ).continuous.comp
        (show Continuous (fun t =>
          ((-I*z) • ContinuousLinearMap.fst ℂ ℂ ℂ + (I*(φ t).1) • ContinuousLinearMap.snd ℂ ℂ ℂ,
           (-I*(φ t).2) • ContinuousLinearMap.fst ℂ ℂ ℂ + (I*z) • ContinuousLinearMap.snd ℂ ℂ ℂ)) by fun_prop)
    fun_prop

/-- The solution of the original spectral equation with prescribed initial vector. -/
def classicalSolution (φ : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ) : ℝ → ℂ × ℂ :=
  solution (classicalODECurve φ z) v

@[simp] theorem classicalSolution_zero (φ : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ) :
    classicalSolution φ z v 0 = v := solution_zero _ _

theorem continuous_classicalSolution (φ : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ) :
    Continuous (classicalSolution φ z v) := continuous_solution _ _

/-- The constructed solution satisfies both signed first-order equations, including the endpoints. -/
theorem hasDerivAt_classicalSolution (φ : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ)
    (t : Icc (0 : ℝ) 1) :
    HasDerivAt (classicalSolution φ z v)
      (classicalODECoefficient (φ t) z (classicalSolution φ z v t)) t :=
  hasDerivAt_solution_coe _ _ t

/-- The original physical Zakharov–Shabat expression equals the spectral parameter times the solution. -/
theorem physicalOperator_classicalSolution (φ : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ)
    (t : Icc (0 : ℝ) 1) :
    physicalOperator (extend φ) (classicalSolution φ z v) t = z • classicalSolution φ z v t := by
  have h := hasDerivAt_classicalSolution φ z v t
  simp only [physicalOperator,extend_coe,(HasFDerivAt.hasDerivAt h.fst).deriv,(HasFDerivAt.hasDerivAt h.snd).deriv,classicalODECoefficient_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.toSpanSingleton_apply,one_smul]
  apply Prod.ext <;> dsimp <;> ring_nf <;> simp [I_sq]

/-- The classical initial-value problem is unique among curves continuous up to both endpoints. -/
theorem classicalSolution_unique (φ : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ) (u : ℝ → ℂ × ℂ)
    (hu : ContinuousOn u (Icc 0 1)) (h0 : u 0 = v)
    (hd : ∀ t : Icc (0 : ℝ) 1, t.val ∈ Ioo (0 : ℝ) 1 →
      HasDerivAt u (classicalODECoefficient (φ t) z (u t)) t) :
    EqOn u (classicalSolution φ z v) (Icc 0 1) :=
  solution_unique _ _ _ hu h0 hd

/-- The two normalized columns form the actual classical fundamental matrix. -/
def classicalFundamentalMatrix (φ : Curve (ℂ × ℂ)) (z : ℂ) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(classicalSolution φ z (1,0) t).1, (classicalSolution φ z (0,1) t).1;
     (classicalSolution φ z (1,0) t).2, (classicalSolution φ z (0,1) t).2]

@[simp] theorem classicalFundamentalMatrix_zero (φ : Curve (ℂ × ℂ)) (z : ℂ) :
    classicalFundamentalMatrix φ z 0 = 1 := by
  simp [classicalFundamentalMatrix,Matrix.one_fin_two]

/-- The Wronskian derivative vanishes because the coefficient matrix has trace zero. -/
theorem hasDerivAt_det_classicalFundamentalMatrix (φ : Curve (ℂ × ℂ)) (z : ℂ)
    (t : Icc (0 : ℝ) 1) :
    HasDerivAt (fun s => (classicalFundamentalMatrix φ z s).det) 0 t := by
  have h₁ := hasDerivAt_classicalSolution φ z (1,0) t
  have h₂ := hasDerivAt_classicalSolution φ z (0,1) t
  have h := ((HasFDerivAt.hasDerivAt h₁.fst).mul (HasFDerivAt.hasDerivAt h₂.snd)).sub ((HasFDerivAt.hasDerivAt h₂.fst).mul (HasFDerivAt.hasDerivAt h₁.snd))
  simp only [classicalODECoefficient_apply] at h
  have hz := h.congr_deriv (show _ = (0 : ℂ) by
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.toSpanSingleton_apply,one_smul]
    dsimp
    ring)
  simp only [classicalFundamentalMatrix,Matrix.det_fin_two_of]
  convert! hz using 1

/-- The fundamental matrix has determinant one at every point of the whole interval. -/
theorem det_classicalFundamentalMatrix (φ : Curve (ℂ × ℂ)) (z : ℂ) (t : Icc (0 : ℝ) 1) :
    (classicalFundamentalMatrix φ z t).det = 1 := by
  have hc : Continuous (fun s => (classicalFundamentalMatrix φ z s).det) := by
    simp only [classicalFundamentalMatrix,Matrix.det_fin_two]
    exact ((continuous_classicalSolution φ z (1,0)).fst.mul
      (continuous_classicalSolution φ z (0,1)).snd).sub
      ((continuous_classicalSolution φ z (0,1)).fst.mul (continuous_classicalSolution φ z (1,0)).snd)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le t.property.1
    (hc.continuousOn) (fun s (hs : s ∈ Ioo (0 : ℝ) t.val) =>
      hasDerivAt_det_classicalFundamentalMatrix φ z ⟨s,⟨hs.1.le,hs.2.le.trans t.property.2⟩⟩)
    (continuous_const.intervalIntegrable (0 : ℝ) t.val)
  have he : (classicalFundamentalMatrix φ z t).det - 1 = 0 := by
    simpa only [intervalIntegral.integral_zero,classicalFundamentalMatrix_zero,Matrix.det_one] using hi.symm
  exact sub_eq_zero.mp he

/-- The period-one monodromy matrix is the endpoint fundamental matrix. -/
def classicalMonodromy (φ : Curve (ℂ × ℂ)) (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  classicalFundamentalMatrix φ z 1

/-- The monodromy trace defines the classical discriminant. -/
def classicalDiscriminant (φ : Curve (ℂ × ℂ)) (z : ℂ) : ℂ :=
  (classicalMonodromy φ z).trace

@[simp] theorem det_classicalMonodromy (φ : Curve (ℂ × ℂ)) (z : ℂ) :
    (classicalMonodromy φ z).det = 1 := det_classicalFundamentalMatrix φ z ⟨1,by constructor <;> norm_num⟩

/-- The endpoint characteristic determinant has the trace-discriminant form. -/
theorem det_classicalMonodromy_sub_scalar (φ : Curve (ℂ × ℂ)) (z σ : ℂ) :
    (classicalMonodromy φ z - σ • 1).det = σ^2-σ*classicalDiscriminant φ z+1 := by
  have h := det_classicalMonodromy φ z
  simp only [Matrix.det_fin_two] at h
  simp [Matrix.det_fin_two,Matrix.sub_apply,Matrix.smul_apply,
    classicalDiscriminant,Matrix.trace_fin_two,smul_eq_mul]
  linear_combination h

end NLS.ZakharovShabat
