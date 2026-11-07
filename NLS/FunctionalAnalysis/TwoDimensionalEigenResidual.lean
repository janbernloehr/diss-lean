import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-! The upper-triangular action in a basis beginning with an eigenvector,
including coincident eigenvalues and nonsemisimple operators. -/
noncomputable section
namespace NLS.FunctionalAnalysis

/-- If a two-dimensional operator has the two specified spectral values
and no others, every basis starting with a lambda-plus eigenvector has the
source upper-triangular residual. No semisimplicity is assumed. -/
theorem exists_twoDimensional_eigen_residual {E : Type*}
    [AddCommGroup E] [Module ℂ E] (b : Module.Basis (Fin 2) ℂ E)
    (T : Module.End ℂ E) (lp lm : ℂ) (hplus : T (b 0) = lp • b 0)
    (hminus : ∃ x : E, x ≠ 0 ∧ T x = lm • x)
    (honly : ∀ (mu : ℂ) (x : E), x ≠ 0 → T x = mu • x → mu = lp ∨ mu = lm) :
    ∃ eta : ℂ, T (b 1) = lm • b 1 + eta • b 0 := by
  let eta := b.repr (T (b 1)) 0
  let beta := b.repr (T (b 1)) 1
  have hs (x : E) : (b.repr x 0) • b 0 + (b.repr x 1) • b 1 = x := by
    simpa only [Fin.sum_univ_two] using b.sum_repr x
  have hsecond : T (b 1) = eta • b 0 + beta • b 1 := (hs _).symm
  have haction (x : E) : T x =
      (b.repr x 0 * lp + b.repr x 1 * eta) • b 0 + (b.repr x 1 * beta) • b 1 := by
    calc
      T x = T ((b.repr x 0) • b 0 + (b.repr x 1) • b 1) := congrArg T (hs x).symm
      _ = _ := by rw [map_add,map_smul,map_smul,hplus,hsecond]; module
  have hzero (x : E) : b.repr (T x) 0 = b.repr x 0 * lp + b.repr x 1 * eta := by
    rw [haction]
    simp
  have hone (x : E) : b.repr (T x) 1 = b.repr x 1 * beta := by
    rw [haction]
    simp
  have hbeta : beta = lm := by
    by_cases he : lm = lp
    · by_cases hb : beta = lp
      · exact hb.trans he.symm
      let a := eta / (beta-lp)
      let x := a • b 0 + b 1
      have hx : x ≠ 0 := by
        intro hx0
        have h := congrArg (fun y => b.repr y 1) hx0
        simp [x] at h
      have hxT : T x = beta • x := by
        have ha : a * (beta-lp) = eta := div_mul_cancel₀ eta (sub_ne_zero.mpr hb)
        have has : a*lp+eta = beta*a := by linear_combination -ha
        dsimp only [x]
        rw [map_add,map_smul,hplus,hsecond,smul_add,smul_smul]
        rw [show (a*lp) • b 0 + (eta • b 0 + beta • b 1) =
          (a*lp+eta) • b 0 + beta • b 1 by module,has,smul_smul]
      rcases honly beta x hx hxT with h | h
      · exact h.trans he.symm
      · exact h
    · obtain ⟨x,hx,hTx⟩ := hminus
      have h0 := hzero x
      have h1 := hone x
      rw [hTx] at h0 h1
      simp only [map_smul,Finsupp.smul_apply,smul_eq_mul] at h0 h1
      have hx1 : b.repr x 1 ≠ 0 := by
        intro hx1
        have hz : (lp-lm)*b.repr x 0 = 0 := by rw [hx1] at h0; linear_combination -h0
        have hx0 : b.repr x 0 = 0 := (mul_eq_zero.mp hz).resolve_left
          (sub_ne_zero.mpr (Ne.symm he))
        apply hx
        rw [← hs x,hx0,hx1,zero_smul,zero_smul,add_zero]
      exact mul_right_cancel₀ hx1 (by simpa only [mul_comm] using h1.symm)
  exact ⟨eta,by rw [hsecond,hbeta,add_comm]⟩

end NLS.FunctionalAnalysis
