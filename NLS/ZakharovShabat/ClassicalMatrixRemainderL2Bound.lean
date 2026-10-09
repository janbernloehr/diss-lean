import NLS.ZakharovShabat.ClassicalRemainderL2Bound

/-! # Matrix form of the continuous-potential L2 remainder estimate

Both normalized fundamental columns are assembled into their actual matrix.
The matrix norm in this module is explicitly the elementwise maximum norm.
The arbitrary-L2 construction and the source's matrix norm convention still
need to be addressed before claiming the full printed Lemma G.1.
-/
noncomputable section
open Set Complex MeasureTheory
open NLS.LinearVolterra NLS.FunctionalAnalysis
open scoped Matrix.Norms.Elementwise
namespace NLS.ZakharovShabat

private theorem norm_matrix_columns (u v : ℂ × ℂ) :
    ‖(!![u.1,v.1;u.2,v.2] : Matrix (Fin 2) (Fin 2) ℂ)‖ = max ‖u‖ ‖v‖ := by
  simp only [Matrix.norm_def,Pi.norm_def,Pi.nnnorm_def]
  simp [Fin.univ_succ,Prod.norm_def,max_left_comm,max_assoc]

/-- The actual free diagonal propagator. -/
def classicalFreeMatrix (z : ℂ) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![exp (-I*z*t),0;0,exp (I*z*t)]

/-- The two columns of the actual first Born integral. -/
def classicalFirstBornMatrix (φ : Curve (ℂ × ℂ)) (z : ℂ) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(classicalFirstBornVector φ z (1,0) t).1,(classicalFirstBornVector φ z (0,1) t).1;
     (classicalFirstBornVector φ z (1,0) t).2,(classicalFirstBornVector φ z (0,1) t).2]

/-- The exponentially weighted matrix remainder, with explicit elementwise norm. -/
def classicalNormalizedMatrixRemainder (φ : Curve (ℂ × ℂ)) (z : ℂ) (t : ℝ) : ℝ :=
  Real.exp (-(|z.im| * t))*‖classicalFundamentalMatrix φ z t-classicalFreeMatrix z t‖

/-- The identically weighted first Born matrix. -/
def classicalNormalizedFirstBornMatrix (φ : Curve (ℂ × ℂ)) (z : ℂ) (t : ℝ) : ℝ :=
  Real.exp (-(|z.im| * t))*‖classicalFirstBornMatrix φ z t‖

theorem classicalNormalizedMatrixRemainder_eq_max (φ : Curve (ℂ × ℂ)) (z : ℂ) (t : ℝ) :
    classicalNormalizedMatrixRemainder φ z t =
      max (classicalNormalizedRemainder φ z (1,0) t) (classicalNormalizedRemainder φ z (0,1) t) := by
  have he : classicalFundamentalMatrix φ z t-classicalFreeMatrix z t =
      !![(classicalSolutionRemainder φ z (1,0) t).1,(classicalSolutionRemainder φ z (0,1) t).1;
         (classicalSolutionRemainder φ z (1,0) t).2,(classicalSolutionRemainder φ z (0,1) t).2] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [classicalFundamentalMatrix,classicalFreeMatrix,classicalSolutionRemainder,classicalFreeVector]
  rw [classicalNormalizedMatrixRemainder,he,norm_matrix_columns,mul_max_of_nonneg _ _ (Real.exp_nonneg _)]
  rfl

theorem classicalNormalizedFirstBornMatrix_eq_max (φ : Curve (ℂ × ℂ)) (z : ℂ) (t : ℝ) :
    classicalNormalizedFirstBornMatrix φ z t =
      max (classicalNormalizedFirstBorn φ z (1,0) t) (classicalNormalizedFirstBorn φ z (0,1) t) := by
  rw [classicalNormalizedFirstBornMatrix,classicalFirstBornMatrix,norm_matrix_columns,
    mul_max_of_nonneg _ _ (Real.exp_nonneg _)]
  rfl

/-- Both fundamental columns obey the same A*exp(A) matrix estimate. The
forcing is the actual first Born matrix, not a supplied bound on the solution. -/
theorem classicalNormalizedMatrixRemainder_le_L2_firstBorn
    (φ : Curve (ℂ × ℂ)) (z : ℂ) (t : Icc (0:ℝ) 1) :
    classicalNormalizedMatrixRemainder φ z t ≤ classicalNormalizedFirstBornMatrix φ z t +
      classicalPotentialL2Norm φ*Real.exp (classicalPotentialL2Norm φ)*
        Real.sqrt (∫ s in (0:ℝ)..t.val, (classicalNormalizedFirstBornMatrix φ z s)^2) := by
  have hc : Continuous (classicalNormalizedMatrixRemainder φ z) := by
    simp_rw [show classicalNormalizedMatrixRemainder φ z = fun s =>
      max (classicalNormalizedRemainder φ z (1,0) s) (classicalNormalizedRemainder φ z (0,1) s)
      from funext (classicalNormalizedMatrixRemainder_eq_max φ z)]
    exact (continuous_classicalNormalizedRemainder φ z (1,0)).max
      (continuous_classicalNormalizedRemainder φ z (0,1))
  have hF : Continuous (classicalNormalizedFirstBornMatrix φ z) := by
    simp_rw [show classicalNormalizedFirstBornMatrix φ z = fun s =>
      max (classicalNormalizedFirstBorn φ z (1,0) s) (classicalNormalizedFirstBorn φ z (0,1) s)
      from funext (classicalNormalizedFirstBornMatrix_eq_max φ z)]
    exact (continuous_classicalNormalizedFirstBorn φ z (1,0)).max
      (continuous_classicalNormalizedFirstBorn φ z (0,1))
  apply le_forcing_add_L2_bound _ _ (fun s => ‖extend φ s‖) hc hF (continuous_extend φ).norm
    t (classicalPotentialL2Norm φ) t.property (fun s _ => norm_nonneg _)
    (fun s _ => mul_nonneg (Real.exp_nonneg _) (norm_nonneg _)) (sqrt_integral_potential_norm_sq_le φ t)
  intro s hs
  have hv (v : ℂ × ℂ)
      (hr : ∀ r, classicalNormalizedRemainder φ z v r ≤ classicalNormalizedMatrixRemainder φ z r)
      (hB : classicalNormalizedFirstBorn φ z v s ≤ classicalNormalizedFirstBornMatrix φ z s) :
      classicalNormalizedRemainder φ z v s ≤ classicalNormalizedFirstBornMatrix φ z s +
        ∫ r in (0:ℝ)..s, ‖extend φ r‖*classicalNormalizedMatrixRemainder φ z r := by
    apply (classicalNormalizedRemainder_le_firstBorn_add_variable_integral φ z v
      ⟨s,hs.1,hs.2.trans t.property.2⟩).trans
    exact add_le_add hB (intervalIntegral.integral_mono_on hs.1
      (((continuous_extend φ).norm.mul (continuous_classicalNormalizedRemainder φ z v)).intervalIntegrable 0 s)
      (((continuous_extend φ).norm.mul hc).intervalIntegrable 0 s)
      (fun r _ => mul_le_mul_of_nonneg_left (hr r) (norm_nonneg _)))
  rw [classicalNormalizedMatrixRemainder_eq_max]
  apply max_le
  · exact hv (1,0) (fun r => by rw [classicalNormalizedMatrixRemainder_eq_max]; exact le_max_left _ _)
      (by rw [classicalNormalizedFirstBornMatrix_eq_max]; exact le_max_left _ _)
  · exact hv (0,1) (fun r => by rw [classicalNormalizedMatrixRemainder_eq_max]; exact le_max_right _ _)
      (by rw [classicalNormalizedFirstBornMatrix_eq_max]; exact le_max_right _ _)

end NLS.ZakharovShabat
