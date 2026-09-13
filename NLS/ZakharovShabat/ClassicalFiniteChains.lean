import NLS.ZakharovShabat.ClassicalMonodromyTaylor

/-!
# Classical chains with arbitrary initial jets

Finite original chains have independent initial data at each level. Their
continuous representatives are the convolution of these data with the
normalized zero-initial chains, rather than a single normalized column.
-/

noncomputable section
open Set Complex NLS.LinearVolterra
namespace NLS.ZakharovShabat

/-- A forced solution is the homogeneous initial-value curve plus the zero-initial source solver. -/
theorem classicalForcedSolution_eq_curve_add_chain (Φ : Curve (ℂ × ℂ)) (z : ℂ)
    (g : Curve (ℂ × ℂ)) (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) :
    classicalForcedSolution Φ z g v t =
      (classicalSolutionCurve Φ z v + classicalChainOperator Φ z g) t := by
  rw [ContinuousMap.add_apply,classicalSolutionCurve_apply,classicalChainOperator_apply]
  exact classicalForcedSolution_eq_homogeneous_add Φ z g v t

/-- The classical chain with prescribed initial data at every level. -/
def classicalJetCurve (Φ : Curve (ℂ × ℂ)) (z : ℂ) (v : ℕ → ℂ × ℂ) : ℕ → Curve (ℂ × ℂ)
  | 0 => classicalSolutionCurve Φ z (v 0)
  | n+1 => classicalSolutionCurve Φ z (v (n+1)) + classicalChainOperator Φ z (classicalJetCurve Φ z v n)

@[simp] theorem classicalJetCurve_zero (Φ : Curve (ℂ × ℂ)) (z : ℂ) (v : ℕ → ℂ × ℂ) :
    classicalJetCurve Φ z v 0 = classicalSolutionCurve Φ z (v 0) := rfl

theorem classicalJetCurve_succ (Φ : Curve (ℂ × ℂ)) (z : ℂ) (v : ℕ → ℂ × ℂ) (n : ℕ) :
    classicalJetCurve Φ z v (n+1) =
      classicalSolutionCurve Φ z (v (n+1)) + classicalChainOperator Φ z (classicalJetCurve Φ z v n) := rfl

/-- Every level has exactly the prescribed initial vector. -/
@[simp] theorem classicalJetCurve_initial (Φ : Curve (ℂ × ℂ)) (z : ℂ) (v : ℕ → ℂ × ℂ) (n : ℕ) :
    classicalJetCurve Φ z v n ⟨0,by simp⟩ = v n := by
  cases n with
  | zero => simp [classicalSolution_zero]
  | succ n => simp [classicalJetCurve_succ,classicalChainOperator_apply,classicalSolution_zero]

/-- Successive levels are the actual forced solution with the next prescribed initial value. -/
theorem classicalJetCurve_succ_apply (Φ : Curve (ℂ × ℂ)) (z : ℂ) (v : ℕ → ℂ × ℂ)
    (n : ℕ) (t : Icc (0 : ℝ) 1) :
    classicalJetCurve Φ z v (n+1) t = classicalForcedSolution Φ z (classicalJetCurve Φ z v n) (v (n+1)) t :=
  (classicalForcedSolution_eq_curve_add_chain Φ z _ _ t).symm

/-- The whole chain is the finite convolution of normalized chain curves and initial data. -/
theorem classicalJetCurve_eq_sum (Φ : Curve (ℂ × ℂ)) (z : ℂ) (v : ℕ → ℂ × ℂ) (n : ℕ) :
    classicalJetCurve Φ z v n = ∑ j ∈ Finset.range (n+1), classicalChainCurve Φ z j (v (n-j)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [classicalJetCurve_succ,ih,map_sum]
    rw [Finset.sum_range_succ' (fun j => classicalChainCurve Φ z j (v (n+1-j))) (n+1)]
    simp only [classicalChainCurve_zero,Nat.sub_zero]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [classicalChainCurve_succ,Nat.add_sub_add_right]

/-- A finite initial segment determines the corresponding whole chain curve. -/
theorem classicalJetCurve_congr (Φ : Curve (ℂ × ℂ)) (z : ℂ) (v w : ℕ → ℂ × ℂ) (n : ℕ)
    (h : ∀ j ≤ n, v j = w j) : classicalJetCurve Φ z v n = classicalJetCurve Φ z w n := by
  rw [classicalJetCurve_eq_sum,classicalJetCurve_eq_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [h (n-j) (Nat.sub_le _ _)]

/-- The same two normalized columns propagate every initial vector at every chain level. -/
theorem classicalChainCurve_eq_columns (Φ : Curve (ℂ × ℂ)) (z : ℂ) (n : ℕ) (v : ℂ × ℂ) :
    classicalChainCurve Φ z n v =
      v.1 • classicalChainCurve Φ z n (1,0) + v.2 • classicalChainCurve Φ z n (0,1) := by
  have h : classicalSolutionCurve Φ z v =
      v.1 • classicalSolutionCurve Φ z (1,0) + v.2 • classicalSolutionCurve Φ z (0,1) := by
    apply ContinuousMap.ext
    intro t
    simpa only [ContinuousMap.add_apply,ContinuousMap.smul_apply,classicalSolutionCurve_apply] using
      classicalSolution_eq_columns Φ z v t
  simp only [classicalChainCurve,h,map_add,map_smul]

end NLS.ZakharovShabat
