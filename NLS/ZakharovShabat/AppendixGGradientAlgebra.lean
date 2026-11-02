import NLS.ZakharovShabat.ClassicalHermitianGradientFourier

/-! # The pointwise gradient algebra in Appendix G.5

The physical gradient factors through the terminal fundamental matrix.
The three column-product expansions retain the actual free columns and
their remainders, with the coordinate order of the source star product.
-/
noncomputable section
open Set Complex NLS.ComplexAnalysis NLS.LinearVolterra
namespace NLS.ZakharovShabat

/-- The literal terminal-matrix factorization of i times the physical gradient. -/
theorem appendixG_gradient_matrix_factorization
    (φ : Curve (ℂ × ℂ)) (z : ℂ) (h : ℂ × ℂ) (s : ℝ) :
    let a := classicalSolution φ z (1,0) s
    let b := classicalSolution φ z (0,1) s
    classicalHermitianGradientMatrix φ z h s =
      (hermitianColumns (classicalSolution φ z (1,0) 1)
        (classicalSolution φ z (0,1) 1)).comp
      (hermitianColumns
        (-(a.2*b.2*h.1+a.1*b.1*h.2), a.2^2*h.1+a.1^2*h.2)
        (-(b.2^2*h.1+b.1^2*h.2), a.2*b.2*h.1+a.1*b.1*h.2)) := by
  dsimp only
  ext x
  obtain ⟨v,rfl⟩ := hermitianPairEquiv.symm.surjective x
  apply hermitianPairEquiv.injective
  simp only [classicalHermitianGradientMatrix,ContinuousLinearMap.comp_apply,
    classicalEndpointGradient,ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd']
  simp [hermitianColumns]
  apply Prod.ext <;> simp only [Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
  all_goals ring_nf; simp [I_sq,sub_eq_add_neg]

/-- The first column square splits into its free term, twice its cross term,
and the square of its actual remainder. -/
theorem appendixG_first_column_square
    (φ : Curve (ℂ × ℂ)) (z : ℂ) (s : ℝ) :
    let a := classicalSolution φ z (1,0) s
    let r := classicalSolutionRemainder φ z (1,0) s
    (a.2^2,a.1^2) =
      (0,exp (-I*z*s)^2) + (2 : ℂ) • (0,r.1*exp (-I*z*s)) + (r.2^2,r.1^2) := by
  simp only [classicalSolutionRemainder,classicalFreeVector]
  apply Prod.ext <;> simp
  ring

/-- The mixed column product has zero free term and the two distinct cross terms. -/
theorem appendixG_mixed_column_product
    (φ : Curve (ℂ × ℂ)) (z : ℂ) (s : ℝ) :
    let a := classicalSolution φ z (1,0) s
    let b := classicalSolution φ z (0,1) s
    let r := classicalSolutionRemainder φ z (1,0) s
    let q := classicalSolutionRemainder φ z (0,1) s
    (a.2*b.2,a.1*b.1) =
      (0,q.1*exp (-I*z*s)) + (r.2*exp (I*z*s),0) + (r.2*q.2,r.1*q.1) := by
  simp only [classicalSolutionRemainder,classicalFreeVector]
  apply Prod.ext <;> simp <;> ring

/-- The second column square has the opposite free mode and matching cross term. -/
theorem appendixG_second_column_square
    (φ : Curve (ℂ × ℂ)) (z : ℂ) (s : ℝ) :
    let b := classicalSolution φ z (0,1) s
    let q := classicalSolutionRemainder φ z (0,1) s
    (b.2^2,b.1^2) =
      (exp (I*z*s)^2,0) + (2 : ℂ) • (q.2*exp (I*z*s),0) + (q.2^2,q.1^2) := by
  simp only [classicalSolutionRemainder,classicalFreeVector]
  apply Prod.ext <;> simp
  ring

end NLS.ZakharovShabat
