import NLS.ZakharovShabat.ClassicalHermitianTimeBounds

/-! # The missing remainder hat in the proof of G.3

The displayed uniform time-derivative bound for M is false even for the
zero potential. This audits that proof line, not G.3's remainder conclusions.
-/
noncomputable section
open Set Complex NLS.LinearVolterra NLS.ComplexAnalysis
namespace NLS.ZakharovShabat

/-- The actual fundamental derivative is the free diagonal generator at zero. -/
theorem deriv_classicalHermitianFundamental_zeroPotential_at_zero (z : ℂ) :
    deriv (fun t => classicalHermitianMatrixOperator (classicalFundamentalMatrix 0 z t)) 0 =
      hermitianColumns (-I*z,0) (0,I*z) := by
  have hu := hasDerivAt_classicalSolution 0 z (1,0) ⟨0,by norm_num⟩
  have hv := hasDerivAt_classicalSolution 0 z (0,1) ⟨0,by norm_num⟩
  have h := ((hermitianColumnsCLM.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
    (0 : ℝ) (hu.prodMk hv)).deriv
  simpa [Function.comp_def,hermitianColumnsCLM_apply,classicalHermitianMatrixOperator,
    classicalFundamentalMatrix,classicalODECoefficient_apply] using h

/-- Testing one unit Hermitian vector detects linear spectral growth. -/
theorem norm_deriv_classicalHermitianFundamental_zeroPotential_at_zero_ge (z : ℂ) :
    ‖z‖ ≤ ‖deriv (fun t => classicalHermitianMatrixOperator (classicalFundamentalMatrix 0 z t)) 0‖ := by
  rw [deriv_classicalHermitianFundamental_zeroPotential_at_zero]
  have h := (hermitianColumns (-I*z,0) (0,I*z)).le_opNorm (hermitianPair (1,0))
  simpa [hermitianColumns_apply,hermitianPair_norm,norm_mul] using h

/-- The Hermitian operator norm is exactly the spectral magnitude. -/
theorem norm_deriv_classicalHermitianFundamental_zeroPotential_at_zero (z : ℂ) :
    ‖deriv (fun t => classicalHermitianMatrixOperator (classicalFundamentalMatrix 0 z t)) 0‖ = ‖z‖ := by
  apply le_antisymm ?_ (norm_deriv_classicalHermitianFundamental_zeroPotential_at_zero_ge z)
  rw [deriv_classicalHermitianFundamental_zeroPotential_at_zero]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg z)
  intro w
  obtain ⟨v,rfl⟩ := hermitianPairEquiv.symm.surjective w
  change ‖hermitianColumns (-I*z,0) (0,I*z) (hermitianPair v)‖ ≤ ‖z‖*‖hermitianPair v‖
  rw [hermitianColumns_apply]
  have h := hermitianPair_norm_diagonal_le (-I*z) (I*z) v ‖z‖ (norm_nonneg z)
    (by simp) (by simp)
  simpa [smul_eq_mul,mul_comm] using h

/-- The un-hatted uniform bound printed in the proof of G.3 fails even at zero potential. -/
theorem sourceG3_printed_full_derivative_false :
    ¬ ∃ C : ℝ, ∀ x : ℝ, 1 ≤ |x| → ∀ t ∈ Icc (0 : ℝ) 1,
      Real.exp (-(|(x : ℂ).im| * t))*
        ‖deriv (fun s => classicalHermitianMatrixOperator (classicalFundamentalMatrix 0 (x : ℂ) s)) t‖ ≤ C := by
  rintro ⟨C,hC⟩
  let x := |C|+2
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hx1 : 1 ≤ |x| := by rw [abs_of_nonneg hx]; dsimp [x]; linarith [abs_nonneg C]
  have h := hC x hx1 0 (by simp)
  simp only [Complex.ofReal_im,abs_zero,zero_mul,neg_zero,Real.exp_zero,one_mul] at h
  have hl := (norm_deriv_classicalHermitianFundamental_zeroPotential_at_zero_ge (x : ℂ)).trans h
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hx] at hl
  dsimp [x] at hl
  linarith [le_abs_self C]

end NLS.ZakharovShabat
