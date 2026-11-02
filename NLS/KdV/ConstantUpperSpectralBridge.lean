import NLS.ZakharovShabat.ClassicalBoundaryDeterminants

/-! # The actual constant-upper ZS solutions satisfy the Hill equation

For the continuous potential pair (-1,-q), the first component solves
-y''+q*y=z^2*y. The state transformation is invertible even at z=0.
This bridge reuses the existing IVP construction and does not construct
spectral gap labels, actions, or a second Birkhoff foundation.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology NLS.ZakharovShabat
namespace NLS.KdV

/-- The literal continuous ZS potential with constant upper off-diagonal. -/
def constantUpperPotential (q : NLS.LinearVolterra.Curve ℂ) :
    NLS.LinearVolterra.Curve (ℂ × ℂ) :=
  ⟨fun t => (-1,-q t), continuous_const.prodMk q.continuous.neg⟩

@[simp] theorem constantUpperPotential_apply (q : NLS.LinearVolterra.Curve ℂ)
    (t : Icc (0 : ℝ) 1) : constantUpperPotential q t = (-1,-q t) := rfl

/-- Position of the actual constructed ZS solution. -/
def constantUpperPosition (q : NLS.LinearVolterra.Curve ℂ) (z : ℂ) (v : ℂ × ℂ) : ℝ → ℂ :=
  fun x => (classicalSolution (constantUpperPotential q) z v x).1

/-- The first-order change from ZS coordinates to scalar position/derivative. -/
def constantUpperStateMap (z : ℂ) : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) :=
  (ContinuousLinearMap.fst ℂ ℂ ℂ).prod
    ((-I*z) • ContinuousLinearMap.fst ℂ ℂ ℂ + (-I) • ContinuousLinearMap.snd ℂ ℂ ℂ)

@[simp] theorem constantUpperStateMap_apply (z : ℂ) (v : ℂ × ℂ) :
    constantUpperStateMap z v = (v.1, (-I*z)*v.1 + (-I)*v.2) := rfl

/-- Initial ZS vector for an arbitrary prescribed Hill position and derivative. -/
def constantUpperInitialVector (z : ℂ) (w : ℂ × ℂ) : ℂ × ℂ :=
  (w.1, I*w.2-z*w.1)

theorem constantUpperStateMap_initialVector (z : ℂ) (w : ℂ × ℂ) :
    constantUpperStateMap z (constantUpperInitialVector z w) = w := by
  apply Prod.ext
  · rfl
  · simp only [constantUpperStateMap_apply, constantUpperInitialVector]
    ring_nf
    simp [I_sq]

theorem constantUpperInitialVector_stateMap (z : ℂ) (v : ℂ × ℂ) :
    constantUpperInitialVector z (constantUpperStateMap z v) = v := by
  apply Prod.ext
  · rfl
  · simp only [constantUpperStateMap_apply, constantUpperInitialVector]
    ring_nf
    simp [I_sq]

theorem constantUpperStateMap_injective (z : ℂ) : Function.Injective (constantUpperStateMap z) :=
  Function.LeftInverse.injective (constantUpperInitialVector_stateMap z)

/-- The actual position derivative, including both interval endpoints. -/
theorem hasDerivAt_constantUpperPosition (q : NLS.LinearVolterra.Curve ℂ)
    (z : ℂ) (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) :
    HasDerivAt (constantUpperPosition q z v)
      ((constantUpperStateMap z (classicalSolution (constantUpperPotential q) z v t)).2) t := by
  have h := HasFDerivAt.hasDerivAt (hasDerivAt_classicalSolution (constantUpperPotential q) z v t).fst
  simpa [constantUpperPosition, classicalODECoefficient_apply, constantUpperStateMap_apply] using! h

/-- No derivative of q is needed for the second derivative of the actual
scalar solution: continuity of the original coefficient is sufficient. -/
theorem hasDerivAt_deriv_constantUpperPosition (q : NLS.LinearVolterra.Curve ℂ)
    (z : ℂ) (v : ℂ × ℂ) (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (deriv (constantUpperPosition q z v))
      ((q ⟨x,hx.1.le,hx.2.le⟩ - z^2) * constantUpperPosition q z v x) x := by
  let t : Icc (0 : ℝ) 1 := ⟨x,hx.1.le,hx.2.le⟩
  have hs := hasDerivAt_classicalSolution (constantUpperPotential q) z v t
  have hd := ((HasFDerivAt.hasDerivAt hs.fst).const_mul (-I*z)).add
    ((HasFDerivAt.hasDerivAt hs.snd).const_mul (-I))
  have he : deriv (constantUpperPosition q z v) =ᶠ[𝓝 x]
      (fun y => (-I*z)*(classicalSolution (constantUpperPotential q) z v y).1 +
        (-I)*(classicalSolution (constantUpperPotential q) z v y).2) := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    exact (hasDerivAt_constantUpperPosition q z v ⟨y,hy.1.le,hy.2.le⟩).deriv
  have hsecond := hd.congr_of_eventuallyEq he
  convert! hsecond using 1
  simp only [classicalODECoefficient_apply, constantUpperPotential_apply]
  dsimp [constantUpperPosition, t]
  ring_nf
  simp [I_sq]
  ring

/-- The actual constructed solution satisfies the physical scalar Hill equation. -/
theorem hill_equation_constantUpperPosition (q : NLS.LinearVolterra.Curve ℂ)
    (z : ℂ) (v : ℂ × ℂ) (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
    -deriv (deriv (constantUpperPosition q z v)) x +
      q ⟨x,hx.1.le,hx.2.le⟩ * constantUpperPosition q z v x =
        z^2 * constantUpperPosition q z v x := by
  rw [(hasDerivAt_deriv_constantUpperPosition q z v x hx).deriv]
  ring

/-- The actual position and its actual derivative form the transformed state. -/
def constantUpperHillState (q : NLS.LinearVolterra.Curve ℂ) (z : ℂ) (v : ℂ × ℂ)
    (x : ℝ) : ℂ × ℂ :=
  (constantUpperPosition q z v x, deriv (constantUpperPosition q z v) x)

theorem constantUpperHillState_eq (q : NLS.LinearVolterra.Curve ℂ)
    (z : ℂ) (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) :
    constantUpperHillState q z v t =
      constantUpperStateMap z (classicalSolution (constantUpperPotential q) z v t) := by
  exact Prod.ext rfl (hasDerivAt_constantUpperPosition q z v t).deriv

/-- Prescribing scalar initial data does not restrict their possible values. -/
theorem constantUpperHillState_initial (q : NLS.LinearVolterra.Curve ℂ)
    (z : ℂ) (w : ℂ × ℂ) :
    constantUpperHillState q z (constantUpperInitialVector z w) 0 = w := by
  have h := constantUpperHillState_eq q z (constantUpperInitialVector z w)
    ⟨0,by constructor <;> norm_num⟩
  simpa only [classicalSolution_zero, constantUpperStateMap_initialVector] using h

/-- Every Floquet multiplier transfers in both directions, for all z,
including z=0, with no endpoint condition on q needed by the state map. -/
theorem constantUpper_floquet_condition_iff (q : NLS.LinearVolterra.Curve ℂ)
    (z μ : ℂ) (v : ℂ × ℂ) :
    classicalSolution (constantUpperPotential q) z v 1 = μ • v ↔
      constantUpperHillState q z v 1 = μ • constantUpperHillState q z v 0 := by
  have h0 := constantUpperHillState_eq q z v ⟨0,by constructor <;> norm_num⟩
  have h1 := constantUpperHillState_eq q z v ⟨1,by constructor <;> norm_num⟩
  simp only [classicalSolution_zero] at h0
  change constantUpperHillState q z v 0 = constantUpperStateMap z v at h0
  change constantUpperHillState q z v 1 =
    constantUpperStateMap z (classicalSolution (constantUpperPotential q) z v 1) at h1
  rw [h1, h0, ← map_smul]
  exact ⟨fun h => congrArg (constantUpperStateMap z) h,
    fun h => constantUpperStateMap_injective z h⟩

/-- Trace of the two scalar Hill solutions with normalized initial
position/derivative vectors (1,0) and (0,1), using their actual derivatives. -/
def constantUpperHillTrace (q : NLS.LinearVolterra.Curve ℂ) (z : ℂ) : ℂ :=
  (constantUpperHillState q z (constantUpperInitialVector z (1,0)) 1).1 +
  (constantUpperHillState q z (constantUpperInitialVector z (0,1)) 1).2

/-- The normalized scalar trace equals the actual ZS discriminant, for
the energy parameter lambda=z^2, including z=0. -/
theorem constantUpperHillTrace_eq_discriminant (q : NLS.LinearVolterra.Curve ℂ) (z : ℂ) :
    constantUpperHillTrace q z = classicalDiscriminant (constantUpperPotential q) z := by
  let t : Icc (0 : ℝ) 1 := ⟨1,by constructor <;> norm_num⟩
  have h1 := constantUpperHillState_eq q z (constantUpperInitialVector z (1,0)) t
  have h2 := constantUpperHillState_eq q z (constantUpperInitialVector z (0,1)) t
  unfold constantUpperHillTrace
  rw [h1, h2, classicalSolution_eq_columns (constantUpperPotential q) z
      (constantUpperInitialVector z (1,0)) t,
    classicalSolution_eq_columns (constantUpperPotential q) z
      (constantUpperInitialVector z (0,1)) t]
  simp [constantUpperStateMap_apply, constantUpperInitialVector,
    classicalDiscriminant, classicalMonodromy, classicalFundamentalMatrix,
    Matrix.trace_fin_two, t, smul_eq_mul]
  ring_nf
  simp [I_sq]

end NLS.KdV
