import NLS.Dynamics.HamiltonianPhaseFlow

/-! # Full-norm time derivatives of finitely supported phase trajectories

Finite Birkhoff support permits differentiation in the entire Banach
sequence norm, even when the frequency sequence is unbounded.
-/
noncomputable section
open Complex
open scoped ENNReal
namespace NLS.Birkhoff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The finite sum of the Hamiltonian coordinate velocities. -/
def finiteHamiltonianPhaseVelocity (freq : ℤ → ℝ) (S : Finset ℤ)
    (z : Coeff p × Coeff p) : Coeff p × Coeff p :=
  (∑ n ∈ S, lp.single p n (-I*(freq n : ℂ)*z.1 n),
   ∑ n ∈ S, lp.single p n (I*(freq n : ℂ)*z.2 n))

omit [Fact (1 ≤ p)] in
/-- Evaluation of the first finite phase velocity. -/
@[simp] theorem finiteHamiltonianPhaseVelocity_fst (freq : ℤ → ℝ) (S : Finset ℤ)
    (z : Coeff p × Coeff p) (n : ℤ) :
    (finiteHamiltonianPhaseVelocity freq S z).1 n =
      if n ∈ S then -I*(freq n : ℂ)*z.1 n else 0 := by
  change (lp.evalₗ (𝕜 := ℂ) (fun _ : ℤ => ℂ) p n)
    (∑ k ∈ S, lp.single p k (-I*(freq k : ℂ)*z.1 k)) = _
  rw [map_sum]
  by_cases hn : n ∈ S <;> simp [lp.evalₗ_apply,lp.single_apply,Pi.single_apply,hn]

omit [Fact (1 ≤ p)] in
/-- Evaluation of the second finite phase velocity. -/
@[simp] theorem finiteHamiltonianPhaseVelocity_snd (freq : ℤ → ℝ) (S : Finset ℤ)
    (z : Coeff p × Coeff p) (n : ℤ) :
    (finiteHamiltonianPhaseVelocity freq S z).2 n =
      if n ∈ S then I*(freq n : ℂ)*z.2 n else 0 := by
  change (lp.evalₗ (𝕜 := ℂ) (fun _ : ℤ => ℂ) p n)
    (∑ k ∈ S, lp.single p k (I*(freq k : ℂ)*z.2 k)) = _
  rw [map_sum]
  by_cases hn : n ∈ S <;> simp [lp.evalₗ_apply,lp.single_apply,Pi.single_apply,hn]

omit [Fact (1 ≤ p)] in
private theorem sum_single_of_support (S : Finset ℤ) (a : Coeff p)
    (ha : ∀ n ∉ S, a n = 0) : (∑ n ∈ S, lp.single p n (a n)) = a := by
  ext n
  change (lp.evalₗ (𝕜 := ℂ) (fun _ : ℤ => ℂ) p n) (∑ j ∈ S, lp.single p j (a j)) = _
  rw [map_sum]
  by_cases hn : n ∈ S
  · simp [lp.evalₗ_apply,lp.single_apply,Pi.single_apply,hn]
  · simp [lp.evalₗ_apply,lp.single_apply,Pi.single_apply,hn,ha n hn]

/-- Finite coordinate support gives the actual derivative in the full sequence norm. -/
theorem hasDerivAt_hamiltonianPhaseFlow_of_support (freq : ℤ → ℝ)
    (S : Finset ℤ) (z : Coeff p × Coeff p)
    (hz : ∀ n ∉ S, z.1 n = 0 ∧ z.2 n = 0) (t : ℝ) :
    HasDerivAt (fun τ => hamiltonianPhaseFlow freq τ z)
      (finiteHamiltonianPhaseVelocity freq S (hamiltonianPhaseFlow freq t z)) t := by
  have hzero (τ : ℝ) (n : ℤ) (hn : n ∉ S) :
      (hamiltonianPhaseFlow freq τ z).1 n = 0 ∧ (hamiltonianPhaseFlow freq τ z).2 n = 0 := by
    simp only [hamiltonianPhaseFlow_fst,hamiltonianPhaseFlow_snd,(hz n hn).1,(hz n hn).2,mul_zero,and_self]
  have hd₁ := HasDerivAt.fun_sum (u := S) (fun n _ =>
    (lp.singleContinuousLinearMap ℝ (fun _ : ℤ => ℂ) p n).hasFDerivAt.comp_hasDerivAt t
      (hasDerivAt_hamiltonianPhaseFlow_fst freq z n t))
  have hd₂ := HasDerivAt.fun_sum (u := S) (fun n _ =>
    (lp.singleContinuousLinearMap ℝ (fun _ : ℤ => ℂ) p n).hasFDerivAt.comp_hasDerivAt t
      (hasDerivAt_hamiltonianPhaseFlow_snd freq z n t))
  have he₁ : (fun τ => ∑ n ∈ S, lp.single p n ((hamiltonianPhaseFlow freq τ z).1 n)) =
      fun τ => (hamiltonianPhaseFlow freq τ z).1 :=
    funext (fun τ => sum_single_of_support S _ (fun n hn => (hzero τ n hn).1))
  have he₂ : (fun τ => ∑ n ∈ S, lp.single p n ((hamiltonianPhaseFlow freq τ z).2 n)) =
      fun τ => (hamiltonianPhaseFlow freq τ z).2 :=
    funext (fun τ => sum_single_of_support S _ (fun n hn => (hzero τ n hn).2))
  simp only [Function.comp_def,lp.singleContinuousLinearMap_apply,he₁] at hd₁
  simp only [Function.comp_def,lp.singleContinuousLinearMap_apply,he₂] at hd₂
  exact hd₁.prodMk hd₂

end NLS.Birkhoff
