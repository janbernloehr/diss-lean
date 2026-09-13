import NLS.FunctionalAnalysis.FiniteSpectralTrace

/-!
# Analytic finite-dimensional spectral determinants

The determinant is analytic in an operator family on a fixed finite-dimensional
space. Shifting by the spectral parameter gives joint analyticity without any
choice of individual eigenvalues.
-/

noncomputable section
namespace NLS.FiniteSpectralDeterminant
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- Determinants of analytic finite-dimensional operator families are analytic. -/
theorem analyticAt_det {A : X → E →L[ℂ] E} {x : X} (hA : AnalyticAt ℂ A x) :
    AnalyticAt ℂ (fun y => (A y).toLinearMap.det) x := by
  classical
  let b := Module.finBasis ℂ E
  let entry (i j : Fin (Module.finrank ℂ E)) : (E →L[ℂ] E) →L[ℂ] ℂ :=
    LinearMap.toContinuousLinearMap
      { toFun := fun T => b.repr (T (b j)) i
        map_add' := by intros; simp
        map_smul' := by intros; simp }
  have he (i j : Fin (Module.finrank ℂ E)) :
      AnalyticAt ℂ (fun y => LinearMap.toMatrix b b (A y).toLinearMap i j) x := by
    simpa only [Function.comp_def, entry, LinearMap.coe_toContinuousLinearMap',
      LinearMap.coe_mk, AddHom.coe_mk, LinearMap.toMatrix_apply, ContinuousLinearMap.coe_coe] using
      ((entry i j).analyticAt _ |>.comp hA)
  have hd : (fun y => (A y).toLinearMap.det) =
      (fun y => ∑ σ : Equiv.Perm (Fin (Module.finrank ℂ E)),
        ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, LinearMap.toMatrix b b (A y).toLinearMap (σ i) i) := by
    funext y
    rw [← LinearMap.det_toMatrix b, Matrix.det_apply']
  rw [hd]
  exact Finset.analyticAt_fun_sum _ (fun σ _ => analyticAt_const.mul
    (Finset.analyticAt_fun_prod _ (fun i _ => he (σ i) i)))

/-- Spectral shifts preserve analyticity even where the determinant vanishes. -/
theorem analyticAt_shifted_det {A : X → E →L[ℂ] E} {z : X → ℂ} {x : X}
    (hA : AnalyticAt ℂ A x) (hz : AnalyticAt ℂ z x) :
    AnalyticAt ℂ (fun y => ((A y).toLinearMap - z y • 1).det) x := by
  simpa using analyticAt_det (hA.sub (hz.smul (analyticAt_const (v := (1 : E →L[ℂ] E)))))

omit [FiniteDimensional ℂ E] in
/-- Algebraic projection transport preserves spectral shifts and their determinants. -/
theorem shifted_det_conj {V : Type*} [AddCommGroup V] [Module ℂ V]
    (e : E ≃ₗ[ℂ] V) (A : Module.End ℂ E) (z : ℂ) :
    (e.conjAlgEquiv ℂ A-z • 1).det = (A-z • 1).det := by
  have hs : e.conjAlgEquiv ℂ (A-z • 1) = e.conjAlgEquiv ℂ A-z • 1 := by simp
  rw [← hs]
  simpa only [LinearEquiv.conjAlgEquiv_apply, LinearEquiv.conj_apply] using LinearMap.det_conj (A-z • 1) e

/-- The determinant uses the original `(root-z)` orientation and counts all repeated roots. -/
theorem shifted_det_eq_prod_roots (A : Module.End ℂ E) (z : ℂ) :
    (A-z • 1).det = ∏ a ∈ A.charpoly.roots.toFinset, (a-z)^A.charpoly.rootMultiplicity a := by
  classical
  have hs : A.charpoly.Splits := IsAlgClosed.splits _
  have he : A-z • 1 = -(algebraMap ℂ (Module.End ℂ E) z - A) := by
    rw [Algebra.algebraMap_eq_smul_one]
    abel
  rw [he, ← neg_one_smul ℂ (algebraMap ℂ (Module.End ℂ E) z - A), LinearMap.det_smul, ← LinearMap.eval_charpoly,
    hs.eval_eq_prod_roots_of_monic A.charpoly_monic]
  have hm : (A.charpoly.roots.map (fun a => a-z)).prod =
      (-1 : ℂ)^A.charpoly.roots.card * (A.charpoly.roots.map (fun a => z-a)).prod := by
    have hf : (fun a : ℂ => a-z) = (fun a => (-1 : ℂ)*(z-a)) := by funext a; ring
    rw [hf, Multiset.prod_map_mul]
    simp
  rw [← A.charpoly_natDegree, hs.natDegree_eq_card_roots, ← hm,
    Finset.prod_multiset_map_count]
  simp only [Polynomial.count_roots]

end NLS.FiniteSpectralDeterminant
