import NLS.ZakharovShabat.ClassicalChainTaylor

/-!
# Monodromy Taylor coefficients from normalized classical chains

Evaluation of the two normalized chain columns gives the Taylor series of the
fundamental matrix and its endpoint monodromy. Subtracting a fixed multiplier
changes only the constant coefficient of the boundary characteristic matrix.
-/

noncomputable section
open Set Complex Matrix NLS.LinearVolterra
open scoped Matrix.Norms.Elementwise
namespace NLS.ZakharovShabat

private def matrixFromColumns : ((ℂ × ℂ) × (ℂ × ℂ)) →L[ℂ] Matrix (Fin 2) (Fin 2) ℂ :=
  ( { toFun := fun u => !![u.1.1,u.2.1;u.1.2,u.2.2]
      map_add' := by intro u v; ext i j; fin_cases i <;> fin_cases j <;> rfl
      map_smul' := by intro c u; ext i j; fin_cases i <;> fin_cases j <;> rfl } :
      ((ℂ × ℂ) × (ℂ × ℂ)) →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ).toContinuousLinearMap

private def curveColumnsAt (t : Icc (0 : ℝ) 1) :
    (Curve (ℂ × ℂ) × Curve (ℂ × ℂ)) →L[ℂ] Matrix (Fin 2) (Fin 2) ℂ :=
  matrixFromColumns.comp ((ContinuousMap.evalCLM ℂ t).prodMap (ContinuousMap.evalCLM ℂ t))

/-- The two normalized chain columns at a given physical point. -/
def classicalChainMatrix (Φ : Curve (ℂ × ℂ)) (z : ℂ) (n : ℕ) (t : Icc (0 : ℝ) 1) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  curveColumnsAt t (classicalChainCurve Φ z n (1,0),classicalChainCurve Φ z n (0,1))

/-- The zeroth chain matrix is the actual fundamental matrix. -/
@[simp] theorem classicalChainMatrix_zero (Φ : Curve (ℂ × ℂ)) (z : ℂ) (t : Icc (0 : ℝ) 1) :
    classicalChainMatrix Φ z 0 t = classicalFundamentalMatrix Φ z t := by
  change !![(classicalChainCurve Φ z 0 (1,0) t).1,(classicalChainCurve Φ z 0 (0,1) t).1;
    (classicalChainCurve Φ z 0 (1,0) t).2,(classicalChainCurve Φ z 0 (0,1) t).2] = _
  simp only [classicalChainCurve_zero,classicalSolutionCurve_apply]
  rfl

/-- The fundamental-matrix series obtained by taking both chain columns. -/
def classicalFundamentalSeries (Φ : Curve (ℂ × ℂ)) (z : ℂ) (t : Icc (0 : ℝ) 1) :
    FormalMultilinearSeries ℂ ℂ (Matrix (Fin 2) (Fin 2) ℂ) :=
  (curveColumnsAt t).compFormalMultilinearSeries
    ((classicalChainSeries Φ z (1,0)).prod (classicalChainSeries Φ z (0,1)))

/-- Every matrix coefficient is the signed pair of normalized chain columns. -/
theorem classicalFundamentalSeries_apply (Φ : Curve (ℂ × ℂ)) (z : ℂ) (t : Icc (0 : ℝ) 1)
    (n : ℕ) (w : Fin n → ℂ) :
    classicalFundamentalSeries Φ z t n w = (∏ i, w i) • ((-1 : ℂ)^n • classicalChainMatrix Φ z n t) := by
  change curveColumnsAt t (classicalChainSeries Φ z (1,0) n w,classicalChainSeries Φ z (0,1) n w) = _
  rw [classicalChainSeries_apply,classicalChainSeries_apply]
  change curveColumnsAt t ((∏ i, w i) • ((-1 : ℂ)^n •
    (classicalChainCurve Φ z n (1,0),classicalChainCurve Φ z n (0,1)))) = _
  rw [map_smul,map_smul]
  rfl

/-- The full fundamental matrix has the explicit chain-column power series at each spectral parameter. -/
theorem hasFPowerSeriesOnBall_classicalFundamentalMatrix (Φ : Curve (ℂ × ℂ)) (z : ℂ)
    (t : Icc (0 : ℝ) 1) :
    HasFPowerSeriesOnBall (fun w => classicalFundamentalMatrix Φ w t)
      (classicalFundamentalSeries Φ z t) z (classicalChainRadius Φ z) := by
  have h := (curveColumnsAt t).comp_hasFPowerSeriesOnBall (G := Matrix (Fin 2) (Fin 2) ℂ)
    ((hasFPowerSeriesOnBall_classicalSolutionCurve Φ z (1,0)).prod
      (hasFPowerSeriesOnBall_classicalSolutionCurve Φ z (0,1)))
  have hf : (curveColumnsAt t ∘ fun w =>
      (classicalSolutionCurve Φ w (1,0),classicalSolutionCurve Φ w (0,1))) =
      fun w => classicalFundamentalMatrix Φ w t := by
    funext w
    change !![(classicalSolutionCurve Φ w (1,0) t).1,(classicalSolutionCurve Φ w (0,1) t).1;
      (classicalSolutionCurve Φ w (1,0) t).2,(classicalSolutionCurve Φ w (0,1) t).2] = _
    simp only [classicalSolutionCurve_apply]
    rfl
  have h' := h.congr (g := fun w => classicalFundamentalMatrix Φ w t)
    (fun w _ => by convert! congrFun hf w using 1)
  simpa only [min_self] using! h'

/-- Every spectral derivative of the fundamental matrix is identified by its normalized chain columns. -/
theorem iteratedDeriv_classicalFundamentalMatrix (Φ : Curve (ℂ × ℂ)) (z : ℂ)
    (t : Icc (0 : ℝ) 1) (n : ℕ) :
    iteratedDeriv n (fun w => classicalFundamentalMatrix Φ w t) z =
      n.factorial • ((-1 : ℂ)^n • classicalChainMatrix Φ z n t) := by
  rw [iteratedDeriv_eq_iteratedFDeriv]
  have h := (hasFPowerSeriesOnBall_classicalFundamentalMatrix Φ z t).factorial_smul (F := Matrix (Fin 2) (Fin 2) ℂ) (1 : ℂ) n
  calc
    _ = n.factorial • classicalFundamentalSeries Φ z t n (fun _ => 1) := by exact h.symm
    _ = _ := by rw [classicalFundamentalSeries_apply]; simp

/-- The monodromy has the endpoint chain-column series, with the same positive convergence radius. -/
theorem hasFPowerSeriesOnBall_classicalMonodromy (Φ : Curve (ℂ × ℂ)) (z : ℂ) :
    HasFPowerSeriesOnBall (classicalMonodromy Φ)
      (classicalFundamentalSeries Φ z ⟨1,by constructor <;> norm_num⟩) z (classicalChainRadius Φ z) :=
  hasFPowerSeriesOnBall_classicalFundamentalMatrix Φ z ⟨1,by constructor <;> norm_num⟩

/-- Spectral derivatives of the actual monodromy are the factorial-scaled signed chain endpoints. -/
theorem iteratedDeriv_classicalMonodromy (Φ : Curve (ℂ × ℂ)) (z : ℂ) (n : ℕ) :
    iteratedDeriv n (classicalMonodromy Φ) z = n.factorial • ((-1 : ℂ)^n •
      classicalChainMatrix Φ z n ⟨1,by constructor <;> norm_num⟩) :=
  iteratedDeriv_classicalFundamentalMatrix Φ z ⟨1,by constructor <;> norm_num⟩ n

/-- The spectral series of the actual endpoint characteristic matrix. -/
def classicalBoundarySeries (Φ : Curve (ℂ × ℂ)) (z σ : ℂ) :
    FormalMultilinearSeries ℂ ℂ (Matrix (Fin 2) (Fin 2) ℂ) :=
  classicalFundamentalSeries Φ z ⟨1,by constructor <;> norm_num⟩-
    constFormalMultilinearSeries ℂ ℂ (σ • 1)

/-- Subtracting the boundary multiplier preserves the convergent chain series beyond its constant term. -/
theorem hasFPowerSeriesOnBall_classicalBoundaryMatrix (Φ : Curve (ℂ × ℂ)) (z σ : ℂ) :
    HasFPowerSeriesOnBall (fun w => classicalMonodromy Φ w-σ • 1)
      (classicalBoundarySeries Φ z σ) z (classicalChainRadius Φ z) := by
  have h := (hasFPowerSeriesOnBall_classicalMonodromy Φ z).sub (F := Matrix (Fin 2) (Fin 2) ℂ)
    ((hasFPowerSeriesOnBall_const (𝕜 := ℂ) (c := σ • (1 : Matrix (Fin 2) (Fin 2) ℂ)) (e := z)).mono (classicalChainRadius_pos Φ z) le_top)
  exact h

/-- The constant boundary coefficient is the actual monodromy characteristic matrix. -/
@[simp] theorem classicalBoundarySeries_zero (Φ : Curve (ℂ × ℂ)) (z σ : ℂ) (w : Fin 0 → ℂ) :
    classicalBoundarySeries Φ z σ 0 w = classicalMonodromy Φ z-σ • 1 := by
  change classicalFundamentalSeries Φ z ⟨1,by constructor <;> norm_num⟩ 0 w - σ • 1 = _
  rw [classicalFundamentalSeries_apply]
  simp [classicalMonodromy]

/-- Positive boundary coefficients are exactly the signed normalized chain endpoints. -/
theorem classicalBoundarySeries_succ (Φ : Curve (ℂ × ℂ)) (z σ : ℂ) (n : ℕ) (w : Fin (n+1) → ℂ) :
    classicalBoundarySeries Φ z σ (n+1) w = (∏ i, w i) • ((-1 : ℂ)^(n+1) •
      classicalChainMatrix Φ z (n+1) ⟨1,by constructor <;> norm_num⟩) := by
  change classicalFundamentalSeries Φ z ⟨1,by constructor <;> norm_num⟩ (n+1) w - 0 = _
  rw [sub_zero,classicalFundamentalSeries_apply]

end NLS.ZakharovShabat
