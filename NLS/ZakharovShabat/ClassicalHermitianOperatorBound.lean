import NLS.ZakharovShabat.ClassicalHermitianDuhamel
import NLS.ZakharovShabat.ClassicalMatrixRemainderL2Bound
import NLS.ZakharovShabat.ClassicalBoundaryDeterminants

/-! # The G.1 estimate in the Hermitian operator norm

The operator acts on actual Euclidean two-component vectors. Its columns are
those of the constructed fundamental solution, and its forcing is the actual
first Born integral. The literal Hilbert L2 coefficient A*exp(A) is retained.
The potentials here are continuous; extension to arbitrary L2 is still needed.
-/
noncomputable section
open Set Complex MeasureTheory
open NLS.LinearVolterra NLS.ComplexAnalysis NLS.FunctionalAnalysis
namespace NLS.ZakharovShabat

/-- Interpret a complex matrix as an operator on Hermitian vectors. -/
def classicalHermitianMatrixOperator (M : Matrix (Fin 2) (Fin 2) ℂ) :
    HermitianPair →L[ℂ] HermitianPair := hermitianColumns (M 0 0,M 1 0) (M 0 1,M 1 1)

/-- The actual fundamental-solution remainder as a Hermitian operator. -/
def classicalHermitianRemainderOperator (φ : Curve (ℂ × ℂ)) (z : ℂ) (t : ℝ) :
    HermitianPair →L[ℂ] HermitianPair :=
  hermitianColumns (classicalSolutionRemainder φ z (1,0) t) (classicalSolutionRemainder φ z (0,1) t)

/-- The actual first Born integral as a Hermitian operator. -/
def classicalHermitianFirstBornOperator (φ : Curve (ℂ × ℂ)) (z : ℂ) (t : ℝ) :
    HermitianPair →L[ℂ] HermitianPair :=
  hermitianColumns (classicalFirstBornVector φ z (1,0) t) (classicalFirstBornVector φ z (0,1) t)

/-- The operator is precisely the actual remainder matrix M-E. -/
theorem classicalHermitianRemainderOperator_eq_matrix (φ : Curve (ℂ × ℂ)) (z : ℂ) (t : ℝ) :
    classicalHermitianRemainderOperator φ z t =
      classicalHermitianMatrixOperator (classicalFundamentalMatrix φ z t-classicalFreeMatrix z t) := by
  unfold classicalHermitianRemainderOperator classicalHermitianMatrixOperator
  congr 1 <;> ext <;>
    simp [classicalSolutionRemainder,classicalFreeVector,classicalFundamentalMatrix,classicalFreeMatrix]

/-- The operator uses the actual first Born matrix, not a majorant. -/
theorem classicalHermitianFirstBornOperator_eq_matrix (φ : Curve (ℂ × ℂ)) (z : ℂ) (t : ℝ) :
    classicalHermitianFirstBornOperator φ z t =
      classicalHermitianMatrixOperator (classicalFirstBornMatrix φ z t) := rfl

theorem classicalHermitianRemainderOperator_apply (φ : Curve (ℂ × ℂ)) (z : ℂ)
    (v : ℂ × ℂ) (t : Icc (0:ℝ) 1) :
    classicalHermitianRemainderOperator φ z t (hermitianPair v) =
      hermitianPair (classicalSolutionRemainder φ z v t) := by
  rw [classicalHermitianRemainderOperator,hermitianColumns_apply]
  apply congrArg hermitianPair
  simp only [classicalSolutionRemainder]
  rw [classicalSolution_eq_columns φ z v t]
  ext <;> simp [classicalFreeVector,smul_eq_mul] <;> ring

theorem classicalHermitianFirstBornOperator_apply (φ : Curve (ℂ × ℂ)) (z : ℂ)
    (v : ℂ × ℂ) (t : ℝ) :
    classicalHermitianFirstBornOperator φ z t (hermitianPair v) =
      hermitianPair (classicalFirstBornVector φ z v t) := by
  rw [classicalHermitianFirstBornOperator,hermitianColumns_apply]
  apply congrArg hermitianPair
  ext <;> simp [classicalFirstBornVector,smul_eq_mul] <;> ring

theorem continuous_classicalHermitianRemainderOperator (φ : Curve (ℂ × ℂ)) (z : ℂ) :
    Continuous (classicalHermitianRemainderOperator φ z) := by
  change Continuous (fun t => hermitianColumns (classicalSolutionRemainder φ z (1,0) t)
    (classicalSolutionRemainder φ z (0,1) t))
  simpa only [Function.comp_def] using
    continuous_hermitianColumns.comp ((continuous_classicalSolutionRemainder φ z (1,0)).prodMk
      (continuous_classicalSolutionRemainder φ z (0,1)))

theorem continuous_classicalHermitianFirstBornOperator (φ : Curve (ℂ × ℂ)) (z : ℂ) :
    Continuous (classicalHermitianFirstBornOperator φ z) := by
  change Continuous (fun t => hermitianColumns (classicalFirstBornVector φ z (1,0) t)
    (classicalFirstBornVector φ z (0,1) t))
  simpa only [Function.comp_def] using
    continuous_hermitianColumns.comp ((continuous_classicalFirstBornVector φ z (1,0)).prodMk
      (continuous_classicalFirstBornVector φ z (0,1)))

/-- The weighted genuine Hermitian operator norm of the first Born matrix. -/
def classicalNormalizedHermitianFirstBorn (φ : Curve (ℂ × ℂ)) (z : ℂ) (t : ℝ) : ℝ :=
  Real.exp (-(|z.im| * t))*‖classicalHermitianFirstBornOperator φ z t‖

/-- For the off-diagonal Born matrix the Hermitian operator norm is exactly
the maximum of its two oscillatory integral magnitudes. -/
theorem classicalNormalizedHermitianFirstBorn_eq (φ : Curve (ℂ × ℂ)) (z : ℂ) (t : ℝ) :
    classicalNormalizedHermitianFirstBorn φ z t = Real.exp (-(|z.im| * t))*
      max ‖oscillatoryIntegral (-I*z) t (fun s => (extend φ s).1)‖
        ‖oscillatoryIntegral (I*z) t (fun s => (extend φ s).2)‖ := by
  unfold classicalNormalizedHermitianFirstBorn classicalHermitianFirstBornOperator
  simp only [classicalFirstBornVector,mul_zero,mul_one]
  rw [norm_hermitianColumns_offDiagonal]
  simp only [norm_mul,norm_I,norm_neg,one_mul]

/-- The weighted genuine Hermitian operator norm of the remainder matrix. -/
def classicalNormalizedHermitianRemainder (φ : Curve (ℂ × ℂ)) (z : ℂ) (t : ℝ) : ℝ :=
  Real.exp (-(|z.im| * t))*‖classicalHermitianRemainderOperator φ z t‖

theorem continuous_classicalNormalizedHermitianFirstBorn (φ : Curve (ℂ × ℂ)) (z : ℂ) :
    Continuous (classicalNormalizedHermitianFirstBorn φ z) :=
  (show Continuous (fun t : ℝ => Real.exp (-(|z.im| * t))) by fun_prop).mul
    (continuous_classicalHermitianFirstBornOperator φ z).norm

/-- The vector's actual first Born value is bounded by its operator norm. -/
theorem classicalHermitianFirstBorn_le_operator (φ : Curve (ℂ × ℂ)) (z : ℂ)
    (v : ℂ × ℂ) (t : ℝ) :
    classicalHermitianFirstBorn φ z v t ≤
      classicalNormalizedHermitianFirstBorn φ z t*‖hermitianPair v‖ := by
  have h := (classicalHermitianFirstBornOperator φ z t).le_opNorm (hermitianPair v)
  rw [classicalHermitianFirstBornOperator_apply] at h
  exact (mul_le_mul_of_nonneg_left h (Real.exp_nonneg (-(|z.im| * t)))).trans_eq (by dsimp [classicalNormalizedHermitianFirstBorn]; ring)

private theorem sqrt_integral_mul_sq (F : ℝ → ℝ)
    (T c : ℝ) (hT : 0 ≤ T) (hc : 0 ≤ c) :
    Real.sqrt (∫ s in (0:ℝ)..T, (F s*c)^2) = Real.sqrt (∫ s in (0:ℝ)..T, (F s)^2)*c := by
  simp_rw [mul_pow]
  rw [intervalIntegral.integral_mul_const,Real.sqrt_mul
    (intervalIntegral.integral_nonneg hT (fun s _ => sq_nonneg (F s))),Real.sqrt_sq hc]

/-- G.1 with its exact coefficient in the Hermitian operator norm for the
actual continuous-potential fundamental solution. Zero time, zero frequency,
and complex potentials are all included. -/
theorem classicalHermitianOperator_le_L2_firstBorn
    (φ : Curve (ℂ × ℂ)) (z : ℂ) (t : Icc (0:ℝ) 1) :
    classicalNormalizedHermitianRemainder φ z t ≤ classicalNormalizedHermitianFirstBorn φ z t +
      classicalPotentialL2Norm φ*Real.exp (classicalPotentialL2Norm φ)*
        Real.sqrt (∫ s in (0:ℝ)..t.val, (classicalNormalizedHermitianFirstBorn φ z s)^2) := by
  let F := classicalNormalizedHermitianFirstBorn φ z
  let A := classicalPotentialL2Norm φ
  let B := F t + A*Real.exp A*Real.sqrt (∫ s in (0:ℝ)..t.val, (F s)^2)
  have hF : Continuous F := continuous_classicalNormalizedHermitianFirstBorn φ z
  have hF0 (s : ℝ) : 0 ≤ F s := mul_nonneg (Real.exp_nonneg _) (norm_nonneg _)
  have hB : 0 ≤ B := add_nonneg (hF0 t)
    (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_nonneg _)) (Real.sqrt_nonneg _))
  have hv (v : ℂ × ℂ) : classicalHermitianRemainder φ z v t ≤ B*‖hermitianPair v‖ := by
    have h := le_forcing_add_L2_bound (classicalHermitianRemainder φ z v)
      (fun s => F s*‖hermitianPair v‖) (fun s => ‖extend φ s‖)
      (continuous_classicalHermitianRemainder φ z v) (hF.mul continuous_const) (continuous_extend φ).norm
      t A t.property (fun s _ => norm_nonneg _)
      (fun s _ => mul_nonneg (hF0 s) (norm_nonneg _)) (sqrt_integral_potential_norm_sq_le φ t) (by
        intro s hs
        exact (classicalHermitianRemainder_le_firstBorn_add_integral φ z v
          ⟨s,hs.1,hs.2.trans t.property.2⟩).trans
          (add_le_add (classicalHermitianFirstBorn_le_operator φ z v s) (le_refl _)))
    rw [sqrt_integral_mul_sq F t _ t.property.1 (norm_nonneg _)] at h
    exact h.trans_eq (by dsimp [B]; ring)
  have h := (Real.exp (-(|z.im| * t.val)) • classicalHermitianRemainderOperator φ z t).opNorm_le_bound hB (by
    intro w
    obtain ⟨v,rfl⟩ := hermitianPairEquiv.symm.surjective w
    change ‖(Real.exp (-(|z.im| * t.val)) • classicalHermitianRemainderOperator φ z t)
      (hermitianPair v)‖ ≤ B*‖hermitianPair v‖
    simpa only [smul_apply,norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),
      classicalHermitianRemainderOperator_apply,classicalHermitianRemainder] using hv v)
  simpa only [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),
    classicalNormalizedHermitianRemainder,B,F,A] using h

end NLS.ZakharovShabat
