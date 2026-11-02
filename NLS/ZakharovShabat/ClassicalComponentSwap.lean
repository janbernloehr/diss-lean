import NLS.ZakharovShabat.ClassicalSwapSymmetry
import NLS.ZakharovShabat.ClassicalSeparatedCharacteristics

/-! # Unsigned component exchange and spectral reflection

The mKdV diagonal is fixed by unsigned component exchange. The actual
solution covariance uses the signed vector exchange (y2,-y1), which swaps
Dirichlet and Neumann boundary conditions. No spatial reflection is involved.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.LinearVolterra
namespace NLS.ZakharovShabat

/-- The literal unsigned swap of the two physical potential fields. -/
def classicalComponentSwap (Φ : Curve (ℂ × ℂ)) : Curve (ℂ × ℂ) :=
  ⟨fun t => (Φ t).swap,Φ.continuous.snd.prodMk Φ.continuous.fst⟩

@[simp] theorem classicalComponentSwap_apply (Φ : Curve (ℂ × ℂ)) (t : Icc (0:ℝ) 1) :
    classicalComponentSwap Φ t = (Φ t).swap := rfl

@[simp] theorem classicalComponentSwap_involutive (Φ : Curve (ℂ × ℂ)) :
    classicalComponentSwap (classicalComponentSwap Φ) = Φ := by
  apply ContinuousMap.ext
  intro t
  exact Prod.swap_swap (Φ t)

/-- The signed vector exchange that intertwines the unsigned potential swap. -/
def componentSwapVector (y : ℂ × ℂ) : ℂ × ℂ := (y.2,-y.1)

/-- Covariance of the exact physical first-order differential equation. -/
theorem classicalODECoefficient_componentSwap (φ y : ℂ × ℂ) (z : ℂ) :
    classicalODECoefficient φ z (componentSwapVector y) =
      componentSwapVector (classicalODECoefficient φ.swap (-z) y) := by
  apply Prod.ext <;> simp [classicalODECoefficient_apply,componentSwapVector]
  ring

/-- ODE uniqueness gives the complete solution covariance at every time,
with its initial vector and spectral reflection explicitly retained. -/
theorem classicalSolution_componentSwap (Φ : Curve (ℂ × ℂ)) (z : ℂ)
    (v : ℂ × ℂ) (t : Icc (0:ℝ) 1) :
    classicalSolution Φ z (componentSwapVector v) t =
      componentSwapVector (classicalSolution (classicalComponentSwap Φ) (-z) v t) := by
  let u : ℝ → ℂ × ℂ := fun x => componentSwapVector
    (classicalSolution (classicalComponentSwap Φ) (-z) v x)
  have hu : ContinuousOn u (Icc 0 1) :=
    ((continuous_classicalSolution (classicalComponentSwap Φ) (-z) v).snd.prodMk
      (continuous_classicalSolution (classicalComponentSwap Φ) (-z) v).fst.neg).continuousOn
  have h0 : u 0 = componentSwapVector v := by simp [u,componentSwapVector]
  have hd (x : Icc (0:ℝ) 1) (_hx : x.val ∈ Ioo (0:ℝ) 1) :
      HasDerivAt u (classicalODECoefficient (Φ x) z (u x)) x := by
    have h := hasDerivAt_classicalSolution (classicalComponentSwap Φ) (-z) v x
    have hh := (HasFDerivAt.hasDerivAt h.snd).prodMk (HasFDerivAt.hasDerivAt h.fst).neg
    convert! hh using 1
    apply Prod.ext <;> simp [u,componentSwapVector,classicalODECoefficient_apply,
      ContinuousLinearMap.comp_apply,ContinuousLinearMap.toSpanSingleton_apply]
    ring
  exact (classicalSolution_unique Φ z (componentSwapVector v) u hu h0 hd t.property).symm

/-- The original monodromy transforms by the signed vector exchange. -/
theorem classicalMonodromy_componentSwap (Φ : Curve (ℂ × ℂ)) (z : ℂ) :
    classicalMonodromy (classicalComponentSwap Φ) (-z) =
      !![(classicalMonodromy Φ z) 1 1,-(classicalMonodromy Φ z) 1 0;
        -(classicalMonodromy Φ z) 0 1,(classicalMonodromy Φ z) 0 0] := by
  have h₁ := classicalSolution_componentSwap Φ z (1,0) ⟨1,by norm_num⟩
  have h₂ := classicalSolution_componentSwap Φ z (0,1) ⟨1,by norm_num⟩
  have h₁' : classicalSolution Φ z (0,-1) 1 =
      componentSwapVector (classicalSolution (classicalComponentSwap Φ) (-z) (1,0) 1) := h₁
  have h₂' : classicalSolution Φ z (1,0) 1 =
      componentSwapVector (classicalSolution (classicalComponentSwap Φ) (-z) (0,1) 1) := by
    simpa [componentSwapVector] using h₂
  rw [classicalSolution_eq_columns Φ z (0,-1) ⟨1,by norm_num⟩] at h₁'
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [classicalMonodromy,classicalFundamentalMatrix,componentSwapVector] using
      (congrArg Prod.snd h₁').symm
  · simpa [classicalMonodromy,classicalFundamentalMatrix,componentSwapVector] using
      (neg_eq_iff_eq_neg.mp (congrArg Prod.snd h₂').symm)
  · simpa [classicalMonodromy,classicalFundamentalMatrix,componentSwapVector] using
      (congrArg Prod.fst h₁').symm
  · simpa [classicalMonodromy,classicalFundamentalMatrix,componentSwapVector] using
      (congrArg Prod.fst h₂').symm

/-- The discriminant has the exact reflected spectral argument. -/
theorem classicalDiscriminant_componentSwap (Φ : Curve (ℂ × ℂ)) (z : ℂ) :
    classicalDiscriminant (classicalComponentSwap Φ) (-z) = classicalDiscriminant Φ z := by
  simp [classicalDiscriminant,classicalMonodromy_componentSwap,Matrix.trace_fin_two]
  ring

/-- Component exchange switches the separated boundary condition. -/
def componentSwapBoundary : BoundaryCondition → BoundaryCondition
  | .dirichlet => .neumann
  | .neumann => .dirichlet

@[simp] theorem componentSwapBoundary_involutive (b : BoundaryCondition) :
    componentSwapBoundary (componentSwapBoundary b) = b := by cases b <;> rfl

/-- The physical sine normalization contributes a minus sign while
Dirichlet and Neumann exchange their roles. -/
theorem classicalSeparatedCharacteristic_componentSwap (b : BoundaryCondition)
    (Φ : Curve (ℂ × ℂ)) (z : ℂ) :
    classicalSeparatedCharacteristic b (classicalComponentSwap Φ) (-z) =
      -classicalSeparatedCharacteristic (componentSwapBoundary b) Φ z := by
  cases b <;> simp [classicalSeparatedCharacteristic,classicalMonodromy_componentSwap,
    componentSwapBoundary,BoundaryCondition.extensionSign] <;> ring

/-- The actual off-diagonal anti-discriminant changes sign. -/
theorem classicalAntiDiscriminant_componentSwap (Φ : Curve (ℂ × ℂ)) (z : ℂ) :
    classicalAntiDiscriminant (classicalComponentSwap Φ) (-z) = -classicalAntiDiscriminant Φ z := by
  simp [classicalAntiDiscriminant,classicalMonodromy_componentSwap]

end NLS.ZakharovShabat
