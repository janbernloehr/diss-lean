import NLS.SequenceSpaces.ConjugateDuality
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-! Actual bounded l2 matrix operators from summable squared entries.
All rows act by absolutely convergent unconjugated complex products. -/
noncomputable section
open scoped ENNReal
namespace NLS.Coeff

/-- An actual square-summable row of the original complex matrix. -/
def squareSummableMatrixRow (M : ℤ → ℤ → ℂ)
    (hM : Summable (fun p : ℤ × ℤ => ‖M p.1 p.2‖^2)) (l : ℤ) : Coeff 2 :=
  ⟨M l,by
    change Memℓp (M l) 2
    rw [memℓp_gen_iff (by norm_num : 0 < (2:ℝ≥0∞).toReal)]
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using hM.prod_factor l⟩

@[simp] theorem squareSummableMatrixRow_apply (M : ℤ → ℤ → ℂ)
    (hM : Summable (fun p : ℤ × ℤ => ‖M p.1 p.2‖^2)) (l m : ℤ) :
    squareSummableMatrixRow M hM l m = M l m := rfl

/-- The actual row norm retains exactly the sum of its squared entries. -/
theorem norm_sq_squareSummableMatrixRow (M : ℤ → ℤ → ℂ)
    (hM : Summable (fun p : ℤ × ℤ => ‖M p.1 p.2‖^2)) (l : ℤ) :
    ‖squareSummableMatrixRow M hM l‖^2 = ∑' m : ℤ, ‖M l m‖^2 := by
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two,squareSummableMatrixRow_apply] using
    (lp.hasSum_norm (p := 2) (by norm_num) (squareSummableMatrixRow M hM l)).tsum_eq.symm

/-- The actual family of rows belongs to the Hilbert sum of l2 row spaces. -/
def squareSummableMatrixRows (M : ℤ → ℤ → ℂ)
    (hM : Summable (fun p : ℤ × ℤ => ‖M p.1 p.2‖^2)) :
    lp (fun _ : ℤ => Coeff 2) 2 :=
  ⟨squareSummableMatrixRow M hM,by
    change Memℓp (squareSummableMatrixRow M hM) 2
    rw [memℓp_gen_iff (by norm_num : 0 < (2:ℝ≥0∞).toReal)]
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two,norm_sq_squareSummableMatrixRow] using hM.prod⟩

@[simp] theorem squareSummableMatrixRows_apply (M : ℤ → ℤ → ℂ)
    (hM : Summable (fun p : ℤ × ℤ => ‖M p.1 p.2‖^2)) (l : ℤ) :
    squareSummableMatrixRows M hM l = squareSummableMatrixRow M hM l := rfl

/-- No row mass is lost: the total row-family norm squared is the full matrix sum. -/
theorem norm_sq_squareSummableMatrixRows (M : ℤ → ℤ → ℂ)
    (hM : Summable (fun p : ℤ × ℤ => ‖M p.1 p.2‖^2)) :
    ‖squareSummableMatrixRows M hM‖^2 = ∑' p : ℤ × ℤ, ‖M p.1 p.2‖^2 := by
  have h := (lp.hasSum_norm (p := 2) (by norm_num) (squareSummableMatrixRows M hM)).tsum_eq.symm
  simp only [ENNReal.toReal_ofNat,Real.rpow_two,squareSummableMatrixRows_apply] at h
  rw [h,hM.tsum_prod]
  exact tsum_congr fun l => norm_sq_squareSummableMatrixRow M hM l

/-- The actual matrix sum on an arbitrary full l2 input. -/
def squareSummableMatrixApply (M : ℤ → ℤ → ℂ)
    (hM : Summable (fun p : ℤ × ℤ => ‖M p.1 p.2‖^2)) (x : Coeff 2) : Coeff 2 :=
  ⟨fun l => dualPairing (squareSummableMatrixRow M hM l) x,by
    have hb := ((lp.memℓp (squareSummableMatrixRows M hM)).norm.const_mul ‖x‖)
    apply hb.mono'
    intro l
    simpa only [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)),squareSummableMatrixRows_apply,mul_comm] using
      norm_dualPairing_le (squareSummableMatrixRow M hM l) x⟩

@[simp] theorem squareSummableMatrixApply_apply (M : ℤ → ℤ → ℂ)
    (hM : Summable (fun p : ℤ × ℤ => ‖M p.1 p.2‖^2)) (x : Coeff 2) (l : ℤ) :
    squareSummableMatrixApply M hM x l = dualPairing (squareSummableMatrixRow M hM l) x := rfl

/-- The full operator action is bounded by the exact total row norm. -/
theorem norm_squareSummableMatrixApply_le (M : ℤ → ℤ → ℂ)
    (hM : Summable (fun p : ℤ × ℤ => ‖M p.1 p.2‖^2)) (x : Coeff 2) :
    ‖squareSummableMatrixApply M hM x‖ ≤ ‖squareSummableMatrixRows M hM‖*‖x‖ := by
  have h : ‖squareSummableMatrixApply M hM x‖ ≤ ‖(‖x‖:ℂ) • squareSummableMatrixRows M hM‖ := by
    apply lp.norm_mono (by norm_num : (2:ℝ≥0∞) ≠ 0)
    intro l
    simpa only [lp.coeFn_smul,Pi.smul_apply,norm_smul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg x),squareSummableMatrixApply_apply,squareSummableMatrixRows_apply,mul_comm] using
      norm_dualPairing_le (squareSummableMatrixRow M hM l) x
  simpa only [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg x),mul_comm] using h

/-- A square-summable matrix defines a GENUINE bounded operator on the entire l2 space. -/
def squareSummableMatrixCLM (M : ℤ → ℤ → ℂ)
    (hM : Summable (fun p : ℤ × ℤ => ‖M p.1 p.2‖^2)) : Coeff 2 →L[ℂ] Coeff 2 :=
  LinearMap.mkContinuous
    { toFun := squareSummableMatrixApply M hM
      map_add' x y := by
        ext l
        exact map_add (dualPairing (squareSummableMatrixRow M hM l)) x y
      map_smul' c x := by
        ext l
        exact map_smul (dualPairing (squareSummableMatrixRow M hM l)) c x }
    ‖squareSummableMatrixRows M hM‖ (norm_squareSummableMatrixApply_le M hM)

/-- Every original matrix coefficient acts by its absolutely convergent row sum. -/
theorem squareSummableMatrixCLM_apply (M : ℤ → ℤ → ℂ)
    (hM : Summable (fun p : ℤ × ℤ => ‖M p.1 p.2‖^2)) (x : Coeff 2) (l : ℤ) :
    squareSummableMatrixCLM M hM x l = ∑' m : ℤ, M l m*x m := rfl

/-- Every row sum is absolutely convergent for every l2 input. -/
theorem summable_norm_squareSummableMatrix_row (M : ℤ → ℤ → ℂ)
    (hM : Summable (fun p : ℤ × ℤ => ‖M p.1 p.2‖^2)) (x : Coeff 2) (l : ℤ) :
    Summable (fun m : ℤ => ‖M l m*x m‖) :=
  summable_norm_dualPairing (squareSummableMatrixRow M hM l) x

/-- The operator norm squared is bounded by the FULL squared-entry sum. -/
theorem norm_sq_squareSummableMatrixCLM_le (M : ℤ → ℤ → ℂ)
    (hM : Summable (fun p : ℤ × ℤ => ‖M p.1 p.2‖^2)) :
    ‖squareSummableMatrixCLM M hM‖^2 ≤ ∑' p : ℤ × ℤ, ‖M p.1 p.2‖^2 := by
  have h : ‖squareSummableMatrixCLM M hM‖ ≤ ‖squareSummableMatrixRows M hM‖ :=
    ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (norm_squareSummableMatrixApply_le M hM)
  exact (pow_le_pow_left₀ (norm_nonneg _) h 2).trans_eq (norm_sq_squareSummableMatrixRows M hM)

end NLS.Coeff
