import NLS.FunctionalAnalysis.SquaredNeumann

/-!
# Invariant kernels of convergent even operator series

A closed kernel preserved by the square of an operator is preserved by the
convergent series of its even powers. The statement applies before choosing
an equivalent norm in which the square is small.
-/

noncomputable section
namespace NLS.SquaredNeumann
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Continuous testing of an even operator series commutes with its sum. -/
theorem evenSeries_hasSum_apply (K V : E →L[ℂ] E)
    (hs : HasSum (fun j : ℕ => (K^2)^j) V) (L : E →L[ℂ] F) (f : E) :
    HasSum (fun j : ℕ => L (((K^2)^j) f)) (L (V f)) := by
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply] using
    (L.comp (ContinuousLinearMap.apply ℂ E f)).hasSum hs

/-- An invariant kernel for `K²` is preserved by the convergent even operator series. -/
theorem evenSeries_preserves_kernel (K V : E →L[ℂ] E)
    (hs : HasSum (fun j : ℕ => (K^2)^j) V) (L : E →L[ℂ] F)
    (hL : ∀ f : E, L f = 0 → L (K (K f)) = 0) (f : E) (hf : L f = 0) : L (V f) = 0 := by
  have hj (j : ℕ) : L (((K^2)^j) f) = 0 := by
    induction j with
    | zero => simpa using hf
    | succ j hj =>
      rw [pow_succ', pow_two, mul_apply_eq_comp, mul_apply_eq_comp]
      exact hL _ hj
  have ht := evenSeries_hasSum_apply K V hs L f
  have heq : (fun j : ℕ => L (((K^2)^j) f)) = (fun _ : ℕ => (0 : F)) := funext hj
  rw [heq] at ht
  exact ht.unique hasSum_zero

end NLS.SquaredNeumann
