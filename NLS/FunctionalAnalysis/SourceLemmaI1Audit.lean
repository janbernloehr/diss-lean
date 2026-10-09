import NLS.FunctionalAnalysis.SourceSchurComplement

/-! # A counterexample to the unrestricted forward implication printed in I.1

On C × C take A=D=-Id and B=C=Id. Then Id+T exchanges the two
coordinates, so is invertible, although Id+D is zero. The sufficient
direction and the norm-based corollary I.2 remain valid.
-/
noncomputable section
namespace NLS.SchurComplement

/-- The explicit full operator in the counterexample is coordinate exchange. -/
theorem sourceI1_swap_operator :
    (1+block (-1 : ℂ →L[ℂ] ℂ) 1 1 (-1 : ℂ →L[ℂ] ℂ) : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) =
      (ContinuousLinearEquiv.prodComm ℂ ℂ ℂ).toContinuousLinearMap := by
  ext <;> simp [block_apply]

theorem sourceI1_swap_isUnit : IsUnit (1+block (-1 : ℂ →L[ℂ] ℂ) 1 1 (-1 : ℂ →L[ℂ] ℂ)) := by
  rw [sourceI1_swap_operator,ContinuousLinearMap.isUnit_iff_bijective]
  exact (ContinuousLinearEquiv.prodComm ℂ ℂ ℂ).bijective

/-- The failed implication is independent of how a singular inverse is interpreted. -/
theorem sourceI1_lower_not_isUnit : ¬IsUnit (1+(-1 : ℂ →L[ℂ] ℂ)) := by simp

/-- The printed assertion cannot hold for all bounded block operators, even in dimension two. -/
theorem sourceLemmaI1_printed_false :
    ¬∀ (A B C D : ℂ →L[ℂ] ℂ),
      IsUnit (1+block A B C D) ↔ IsUnit (1+D) ∧ IsUnit (sourceSchur A B C D) := by
  intro h
  exact sourceI1_lower_not_isUnit ((h (-1) 1 1 (-1 : ℂ →L[ℂ] ℂ)).mp sourceI1_swap_isUnit).1

/-- The strict norm condition in I.2 cannot be replaced by a non-strict bound.
The zero off-diagonal blocks keep the displayed Schur expression unambiguous. -/
theorem sourceCorollaryI2_boundary_counterexample :
    ‖(-1 : ℂ →L[ℂ] ℂ)‖ = 1 ∧
    (sourceSchur (0 : ℂ →L[ℂ] ℂ) 0 0 (-1 : ℂ →L[ℂ] ℂ)).toLinearMap.det ≠ 0 ∧
    ¬IsUnit (1+block (0 : ℂ →L[ℂ] ℂ) 0 0 (-1 : ℂ →L[ℂ] ℂ)) := by
  refine ⟨by simp,?_,?_⟩
  · simp [sourceSchur,expression]
  · intro h
    have hi := (ContinuousLinearMap.isUnit_iff_bijective.mp h).1
    have he := hi (show (1+block (0 : ℂ →L[ℂ] ℂ) 0 0 (-1 : ℂ →L[ℂ] ℂ)) (0,0) =
        (1+block (0 : ℂ →L[ℂ] ℂ) 0 0 (-1 : ℂ →L[ℂ] ℂ)) (0,1) by
      simp [block_apply])
    exact zero_ne_one (congrArg Prod.snd he)

end NLS.SchurComplement
