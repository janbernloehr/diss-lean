import NLS.ComplexAnalysis.FormalMatrixReduction

/-!
# General formal matrix Taylor nullities

Diagonal reduction computes every finite nullity for a two-by-two formal
matrix with nonzero determinant, and recovers the determinant order eventually.
-/

noncomputable section
open Complex PowerSeries Matrix
namespace NLS.ComplexAnalysis

/-- A formal matrix with nonzero determinant has two finite scalar orders controlling all its nullities. -/
theorem exists_matrixTaylorNullity_orders (A : Matrix (Fin 2) (Fin 2) (PowerSeries ℂ))
    (hA : A.det ≠ 0) : ∃ a b : ℕ,
      ((a+b : ℕ) : ℕ∞) = A.det.order ∧ ∀ N : ℕ,
      Module.finrank ℂ (LinearMap.ker (matrixTaylorJetMap A N)) = min N a+min N b := by
  obtain ⟨L,R,hL,hR,f,g,he⟩ := exists_formalMatrix_diagonal_reduction A
  have hD : (L*A*R).det ≠ 0 := by
    rw [Matrix.det_mul,Matrix.det_mul]
    exact mul_ne_zero (mul_ne_zero ((Matrix.isUnit_iff_isUnit_det L).mp hL).ne_zero hA)
      ((Matrix.isUnit_iff_isUnit_det R).mp hR).ne_zero
  have hfg : f*g ≠ 0 := by simpa only [he,Matrix.det_fin_two_of,mul_zero,sub_zero] using hD
  have hf : f ≠ 0 := left_ne_zero_of_mul hfg
  have hg : g ≠ 0 := right_ne_zero_of_mul hfg
  refine ⟨f.order.toNat,g.order.toNat,?_,fun N => ?_⟩
  · rw [← order_det_units L A R hL hR,he]
    simp only [Matrix.det_fin_two_of,mul_zero,sub_zero,PowerSeries.order_mul,ENat.natCast_add,
      PowerSeries.coe_toNat_order hf,PowerSeries.coe_toNat_order hg]
  · rw [← finrank_ker_matrixTaylorJetMap_units L A R hL hR N,he]
    exact finrank_ker_matrixTaylorJetMap_diagonal f g _ _
      (PowerSeries.coe_toNat_order hf).symm (PowerSeries.coe_toNat_order hg).symm N

/-- Every nonsingular formal matrix eventually has Taylor nullity equal to its determinant order. -/
theorem eventually_finrank_matrixTaylorKernel_eq_det_order
    (A : Matrix (Fin 2) (Fin 2) (PowerSeries ℂ)) (hA : A.det ≠ 0) :
    ∀ᶠ N : ℕ in Filter.atTop,
      (Module.finrank ℂ (LinearMap.ker (matrixTaylorJetMap A N)) : ℕ∞) = A.det.order := by
  obtain ⟨a,b,hab,hN⟩ := exists_matrixTaylorNullity_orders A hA
  refine Filter.eventually_atTop.mpr ⟨max a b,fun N h => ?_⟩
  rw [hN,min_eq_right ((le_max_left _ _).trans h),min_eq_right ((le_max_right _ _).trans h)]
  exact hab

/-- The determinant order bounds every finite Taylor nullity. -/
theorem finrank_matrixTaylorKernel_le_det_order
    (A : Matrix (Fin 2) (Fin 2) (PowerSeries ℂ)) (hA : A.det ≠ 0) (N : ℕ) :
    (Module.finrank ℂ (LinearMap.ker (matrixTaylorJetMap A N)) : ℕ∞) ≤ A.det.order := by
  obtain ⟨a,b,hab,hN⟩ := exists_matrixTaylorNullity_orders A hA
  rw [hN,← hab]
  exact_mod_cast add_le_add (min_le_right N a) (min_le_right N b)

/-- Taylor kernel dimensions increase with the truncation length for nonsingular formal matrices. -/
theorem monotone_finrank_matrixTaylorKernel
    (A : Matrix (Fin 2) (Fin 2) (PowerSeries ℂ)) (hA : A.det ≠ 0) :
    Monotone (fun N => Module.finrank ℂ (LinearMap.ker (matrixTaylorJetMap A N))) := by
  obtain ⟨a,b,_,hN⟩ := exists_matrixTaylorNullity_orders A hA
  intro M N hMN
  dsimp only
  rw [hN,hN]
  exact add_le_add (min_le_min_right a hMN) (min_le_min_right b hMN)

/-- A singular formal matrix has at least one unconstrained scalar jet at every length. -/
theorem le_finrank_matrixTaylorKernel_of_det_eq_zero
    (A : Matrix (Fin 2) (Fin 2) (PowerSeries ℂ)) (hA : A.det = 0) (N : ℕ) :
    N ≤ Module.finrank ℂ (LinearMap.ker (matrixTaylorJetMap A N)) := by
  obtain ⟨L,R,hL,hR,f,g,he⟩ := exists_formalMatrix_diagonal_reduction A
  have hfg : f*g = 0 := by
    have hd : (L*A*R).det = 0 := by rw [Matrix.det_mul,Matrix.det_mul,hA,mul_zero,zero_mul]
    simpa only [he,Matrix.det_fin_two_of,mul_zero,sub_zero] using hd
  rw [← finrank_ker_matrixTaylorJetMap_units L A R hL hR N,he,
    (diagonalTaylorKernelEquiv f g N).finrank_eq,Module.finrank_prod]
  rcases mul_eq_zero.mp hfg with hf | hg
  · rw [hf,finrank_ker_scalarTaylorJetMap_zero]
    omega
  · rw [hg,finrank_ker_scalarTaylorJetMap_zero]
    omega

/-- A uniform finite nullity bound rules out an identically zero formal determinant. -/
theorem det_ne_zero_of_bounded_matrixTaylorNullity
    (A : Matrix (Fin 2) (Fin 2) (PowerSeries ℂ)) (m : ℕ)
    (hm : ∀ N, Module.finrank ℂ (LinearMap.ker (matrixTaylorJetMap A N)) ≤ m) : A.det ≠ 0 := by
  intro hA
  have h := le_finrank_matrixTaylorKernel_of_det_eq_zero A hA (m+1)
  have h' := hm (m+1)
  omega

end NLS.ComplexAnalysis
