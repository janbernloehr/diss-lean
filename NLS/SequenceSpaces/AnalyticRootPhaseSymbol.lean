import NLS.SequenceSpaces.BoundedAnalyticSymbol

/-! # Actual analytic inverse-root and phase symbols

Uniform bounds for an actual root, reciprocal root and phase give two
native bounded analytic reciprocal symbols. The complex phase is kept
literally, and one domain and bound precede both signs and all indices.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.Coeff

/-- The literal inverse-root times the negative actual phase. -/
def rootPhaseSymbol {E : Type*} (r b : E → ℤ → ℂ) (sign : ℂ) : E → Coeff ⊤ :=
  boundedSymbolRealization (fun x n => (r x n)⁻¹*exp (-sign*I*b x n))

/-- The literal root times the opposite phase, with no new branch choice. -/
def rootPhaseInverseSymbol {E : Type*} (r b : E → ℤ → ℂ) (sign : ℂ) : E → Coeff ⊤ :=
  boundedSymbolRealization (fun x n => r x n*exp (sign*I*b x n))

/-- Both actual symbols are native analytic, bounded and EXACT inverses
on ONE open complex domain, with the original coefficient formulas. -/
theorem analytic_rootPhase_symbols
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (U : Set E) (hU : IsOpen U) (r b : E → ℤ → ℂ)
    (hr : ∀ n, AnalyticOnNhd ℂ (fun x => r x n) U)
    (hb : ∀ n, AnalyticOnNhd ℂ (fun x => b x n) U)
    (R Q B : ℝ) (hR : 0≤R) (hQ : 0≤Q) (_hB : 0≤B)
    (hbound : ∀ x∈U, ∀ n, r x n≠0 ∧ ‖r x n‖≤R ∧ ‖(r x n)⁻¹‖≤Q ∧ ‖b x n‖≤B) :
    ∃ C : ℝ, 0<C ∧ ∀ sign : ℂ, sign=1 ∨ sign=-1 →
      AnalyticOnNhd ℂ (rootPhaseSymbol r b sign) U ∧
      AnalyticOnNhd ℂ (rootPhaseInverseSymbol r b sign) U ∧ ∀ x∈U,
        ‖rootPhaseSymbol r b sign x‖≤C ∧ ‖rootPhaseInverseSymbol r b sign x‖≤C ∧
        ∀ n, rootPhaseSymbol r b sign x n=(r x n)⁻¹*exp (-sign*I*b x n) ∧
          rootPhaseInverseSymbol r b sign x n=r x n*exp (sign*I*b x n) ∧
          rootPhaseSymbol r b sign x n*rootPhaseInverseSymbol r b sign x n=1 := by
  let C := (R+Q+1)*Real.exp B
  have hC : 0<C := by dsimp only [C];positivity
  refine ⟨C,hC,?_⟩
  intro sign hsign
  have hn : ‖sign‖=1 := by rcases hsign with rfl | rfl <;> norm_num
  have he (x : E) (hx : x∈U) (n : ℤ) :
      ‖exp (-sign*I*b x n)‖≤Real.exp B ∧ ‖exp (sign*I*b x n)‖≤Real.exp B := by
    constructor
    · apply (Complex.norm_exp_le_exp_norm _).trans
      apply Real.exp_le_exp.mpr
      simpa only [norm_mul,norm_neg,hn,norm_I,one_mul] using (hbound x hx n).2.2.2
    · apply (Complex.norm_exp_le_exp_norm _).trans
      apply Real.exp_le_exp.mpr
      simpa only [norm_mul,hn,norm_I,one_mul] using (hbound x hx n).2.2.2
  obtain ⟨hm,hmd⟩ := analytic_boundedSymbolRealization U hU
    (fun x n => (r x n)⁻¹*exp (-sign*I*b x n)) C hC.le
    (fun n x hx => ((hr n x hx).inv (hbound x hx n).1).mul
      ((analyticAt_const.mul (hb n x hx)).cexp')) (by
      intro x hx n
      rw [norm_mul]
      exact (mul_le_mul (hbound x hx n).2.2.1 (he x hx n).1 (norm_nonneg _) hQ).trans
        (mul_le_mul_of_nonneg_right (by linarith : Q≤R+Q+1) (Real.exp_pos B).le))
  obtain ⟨hi,hid⟩ := analytic_boundedSymbolRealization U hU
    (fun x n => r x n*exp (sign*I*b x n)) C hC.le
    (fun n x hx => (hr n x hx).mul ((analyticAt_const.mul (hb n x hx)).cexp')) (by
      intro x hx n
      rw [norm_mul]
      exact (mul_le_mul (hbound x hx n).2.1 (he x hx n).2 (norm_nonneg _) hR).trans
        (mul_le_mul_of_nonneg_right (by linarith : R≤R+Q+1) (Real.exp_pos B).le))
  refine ⟨hm,hi,?_⟩
  intro x hx
  refine ⟨(hmd x hx).1,(hid x hx).1,?_⟩
  intro n
  refine ⟨(hmd x hx).2 n,(hid x hx).2 n,?_⟩
  dsimp only [rootPhaseSymbol,rootPhaseInverseSymbol]
  rw [(hmd x hx).2 n,(hid x hx).2 n]
  calc
    _ = ((r x n)⁻¹*r x n)*(exp (-sign*I*b x n)*exp (sign*I*b x n)) := by ring
    _ = 1 := by
      rw [inv_mul_cancel₀ (hbound x hx n).1,←Complex.exp_add,
        show -sign*I*b x n+sign*I*b x n=0 by ring,Complex.exp_zero,one_mul]

end NLS.Coeff
