import NLS.ZakharovShabat.SobolevHamiltonianPhaseTaylor

/-! # The signed next-phase hyperbolic sine estimate

The signed diagonal primitives give the first variation of the next phase, with an order N+2 error on the original Hs source.
-/

noncomputable section
open Set Complex NLS.Fourier
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat

/-- The next hyperbolic sine phase includes the signed diagonal primitives
with an order N+2 error, uniformly through N=s on original source balls. -/
theorem exists_uniform_nlsHamiltonian_sinh_increment_error_bound
    (s N : ℕ) (hs : 1 ≤ s) (hNs : N ≤ s) (R : ℝ) (hR : 0 ≤ R) (H : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ab : SobolevSource s, ‖ab‖ ≤ R → ∀ a b : ℝ → ℂ,
      ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) →
      ∀ z : ℂ, 1 ≤ ‖z‖ → |z.im| ≤ H →
        ‖2*sinh (nlsHamiltonianPhase a b (N+1) z)-2*sinh (nlsHamiltonianPhase a b N z)+
          nlsWKBDiagonalPhasePrimitive a b N z 1-
          nlsWKBDiagonalPhasePrimitive (-b) (-a) N (-z) 1‖ ≤ C*‖(2*I*z)⁻¹‖^(N+2) := by
  obtain ⟨C,hC,h⟩ := exists_uniform_nlsHamiltonianPhase_exp_increment_error_bound s N hs hNs R hR H
  refine ⟨2*C,by positivity,?_⟩
  intro ab hab a b ha hb hpa hpb hca hcb z hz hzH
  have h₁ := h ab hab a b ha hb hpa hpb hca hcb z hz hzH
  let cd : SobolevSource s := (-ab.2,-ab.1)
  have hcd : ‖cd‖ ≤ R := by simpa only [cd,Prod.norm_def,norm_neg,max_comm] using hab
  have hc₁ (j : ℤ) : cd.1.val j = periodOneCoefficient (-b) j := by
    simpa only [cd,WeightedCoeff.neg_val,periodOneCoefficient_neg] using congrArg Neg.neg (hcb j)
  have hc₂ (j : ℤ) : cd.2.val j = periodOneCoefficient (-a) j := by
    simpa only [cd,WeightedCoeff.neg_val,periodOneCoefficient_neg] using congrArg Neg.neg (hca j)
  have h₂ := h cd hcd (-b) (-a) hb.neg ha.neg
    (fun x => congrArg Neg.neg (hpb x)) (fun x => congrArg Neg.neg (hpa x)) hc₁ hc₂
    (-z) (by simpa using hz) (by simpa using hzH)
  rw [nlsHamiltonianPhase_signedSwap a b ha hb hpa hpb,
    nlsHamiltonianPhase_signedSwap a b ha hb hpa hpb] at h₂
  simp only [mul_neg,neg_mul,inv_neg,norm_neg] at h₂
  let u := nlsHamiltonianPhase a b N z
  let v := nlsHamiltonianPhase a b (N+1) z
  let X := exp v-exp u-exp (-I*z)*(v-u)
  let Y := exp (-v)-exp (-u)-exp (I*z)*(-v-(-u))
  have hX : ‖X‖ ≤ C*‖(2*I*z)⁻¹‖^(N+2) := h₁
  have hY : ‖Y‖ ≤ C*‖(2*I*z)⁻¹‖^(N+2) := by simpa only [neg_neg] using h₂
  have he : 2*sinh v-2*sinh u+nlsWKBDiagonalPhasePrimitive a b N z 1-
      nlsWKBDiagonalPhasePrimitive (-b) (-a) N (-z) 1 = X-Y := by
    rw [two_sinh,two_sinh,
      nlsWKBDiagonalPhasePrimitive_one_eq_phase_increment,
      nlsWKBDiagonalPhasePrimitive_one_eq_phase_increment,
      nlsHamiltonianPhase_signedSwap a b ha hb hpa hpb,
      nlsHamiltonianPhase_signedSwap a b ha hb hpa hpb]
    dsimp only [X,Y,u,v]
    simp only [mul_neg]
    ring
  change ‖2*sinh v-2*sinh u+nlsWKBDiagonalPhasePrimitive a b N z 1-
    nlsWKBDiagonalPhasePrimitive (-b) (-a) N (-z) 1‖ ≤ _
  rw [he]
  exact (norm_sub_le X Y).trans ((add_le_add hX hY).trans_eq (by ring))

end NLS.ZakharovShabat
