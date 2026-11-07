import NLS.ZakharovShabat.ClassicalNLSHamiltonians

/-! # Spatial reflection of the entire physical Hamiltonian hierarchy

Riccati recurrence uniqueness fixes the sign of every reflected density.
Changing variables in the literal period-one integral then proves the
Hamiltonian identity without spectral or finite-gap assumptions.
-/
noncomputable section
open Set Complex MeasureTheory intervalIntegral
namespace NLS.ZakharovShabat

theorem nlsRiccatiDensity_midpointReflection (a b : ℝ → ℂ) (n : ℕ) :
    nlsRiccatiDensity (fun x => a (1-x)) (fun x => b (1-x)) n =
      fun x => (-1:ℂ)^n*nlsRiccatiDensity a b n (1-x) := by
  let u : ℕ → ℝ → ℂ := fun k x => (-1:ℂ)^k*nlsRiccatiDensity a b k (1-x)
  have hd (k : ℕ) (x : ℝ) :
      deriv (u k) x = (-1:ℂ)^(k+1)*deriv (nlsRiccatiDensity a b k) (1-x) := by
    dsimp only [u]
    simp only [deriv_const_mul_field',deriv_comp_const_sub,pow_succ]
    ring
  have h0 : u 0 = -(fun x => b (1-x)) := by
    funext x
    simp [u]
  have h1 : u 1 = deriv (u 0) := by
    funext x
    rw [hd]
    simp [u]
  have hrec (k : ℕ) : u (k+2) = deriv (u (k+1)) +
      (fun x => a (1-x)) * ∑ ij ∈ Finset.antidiagonal k, u ij.1*u ij.2 := by
    funext x
    have hs : (∑ ij ∈ Finset.antidiagonal k, (u ij.1*u ij.2) x) =
        (-1:ℂ)^k*∑ ij ∈ Finset.antidiagonal k,
          nlsRiccatiDensity a b ij.1 (1-x)*nlsRiccatiDensity a b ij.2 (1-x) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ij hij
      have he := Finset.mem_antidiagonal.mp hij
      dsimp [u]
      rw [show (-1:ℂ)^k = (-1:ℂ)^ij.1*(-1:ℂ)^ij.2 by rw [← pow_add,he]]
      ring
    change u (k+2) x = deriv (u (k+1)) x+a (1-x)*_
    rw [Finset.sum_apply,hs,hd]
    dsimp only [u]
    rw [nlsRiccatiDensity_succ_succ]
    simp only [Pi.add_apply,Pi.mul_apply,Finset.sum_apply,pow_add,neg_one_sq,mul_one]
    ring
  exact (congrFun (nlsRiccatiDensity_unique _ _ u h0 h1 hrec) n).symm

theorem classicalNLSHamiltonian_midpointReflection (a b : ℝ → ℂ) (k : ℕ) :
    classicalNLSHamiltonian (fun x => a (1-x)) (fun x => b (1-x)) (k+1) =
      (-1:ℂ)^k*classicalNLSHamiltonian a b (k+1) := by
  simp only [classicalNLSHamiltonian,nlsRiccatiDensity_midpointReflection]
  have he (x : ℝ) : a (1-x)*((-1:ℂ)^k*nlsRiccatiDensity a b k (1-x)) =
      (-1:ℂ)^k*(a (1-x)*nlsRiccatiDensity a b k (1-x)) := by ring
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_sub_left (fun x => a x*nlsRiccatiDensity a b k x) 1]
  norm_num only [sub_self,sub_zero]
  ring

end NLS.ZakharovShabat
