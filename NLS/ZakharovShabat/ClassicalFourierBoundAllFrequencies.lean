import NLS.ZakharovShabat.ClassicalShiftedFreeFourierDecay

/-! # Fourier bounds at arbitrary frequencies

These coarse bounds include zero frequency. They control the finite head
of spectral sequences uniformly on potential balls, while G.3 controls the tail.
-/

noncomputable section
open Set NLS.LinearVolterra NLS.Fourier
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- A coarse all-frequency constant for the difference from any free evolution. -/
def classicalFourierReferenceBound {q : ℝ≥0∞} (hq : 1 < q) (M : ℝ) (z w : ℂ) : ℝ :=
  (2*(Real.exp (‖z‖+M)+Real.exp ‖w‖)+
    ((‖z‖+M)*Real.exp (‖z‖+M)+‖w‖*Real.exp ‖w‖))*unitIntervalC1FourierConstant hq

/-- A potential ball controls the actual reference error at every fixed pair of frequencies. -/
theorem norm_classicalFourierReference_le {q : ℝ≥0∞} (hq : 1 < q)
    (M : ℝ) (φ : Curve (ℂ × ℂ)) (hφ : ‖φ‖ ≤ M) (z w : ℂ)
    (v : ℂ × ℂ) (L : (ℂ × ℂ) →L[ℝ] ℂ) (hL : ‖L‖ ≤ 1) :
    ‖unitIntervalC1Coefficients hq (fun t => L (classicalSolution φ z v t-classicalFreeVector w v t))
      (L.contDiff.comp ((contDiff_classicalSolution φ z v).sub (contDiff_classicalFreeVector w v)))‖ ≤
      classicalFourierReferenceBound hq M z w*‖v‖ := by
  let : Fact (1 ≤ q) := ⟨hq.le⟩
  have hM : 0 ≤ M := (norm_nonneg φ).trans hφ
  have hS (t : Icc (0 : ℝ) 1) : ‖classicalSolution φ z v t‖ ≤ Real.exp (‖z‖+M)*‖v‖ := by
    apply (norm_classicalSolution_le_exp_norm φ z v t).trans
    rw [mul_comm (Real.exp _) ‖v‖]
    gcongr
    calc
      _ ≤ (‖z‖+‖φ‖)*1 := mul_le_mul_of_nonneg_left t.property.2 (by positivity)
      _ ≤ _ := by simpa using add_le_add_left hφ ‖z‖
  have hF (t : Icc (0 : ℝ) 1) : ‖classicalFreeVector w v t‖ ≤ Real.exp ‖w‖*‖v‖ := by
    have he : classicalFreeVector w v t = classicalSolution 0 w v t := by
      simp [classicalSolution_free,classicalFreeVector]
    rw [he]
    apply (norm_classicalSolution_le_exp_norm 0 w v t).trans
    simp only [norm_zero,add_zero]
    rw [mul_comm (Real.exp _) ‖v‖]
    gcongr
    exact mul_le_of_le_one_right (norm_nonneg _) t.property.2
  have hdS (t : Icc (0 : ℝ) 1) :
      ‖deriv (classicalSolution φ z v) t‖ ≤ (‖z‖+M)*Real.exp (‖z‖+M)*‖v‖ := by
    rw [(hasDerivAt_classicalSolution φ z v t).deriv]
    apply (norm_classicalODECoefficient_apply_le _ _ _).trans
    calc
      _ ≤ (‖z‖+M)*(Real.exp (‖z‖+M)*‖v‖) :=
        mul_le_mul (add_le_add le_rfl ((φ.norm_coe_le_norm t).trans hφ)) (hS t)
          (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hdF (t : Icc (0 : ℝ) 1) :
      ‖deriv (classicalFreeVector w v) t‖ ≤ ‖w‖*Real.exp ‖w‖*‖v‖ := by
    rw [(hasDerivAt_classicalFreeVector w v t).deriv]
    apply norm_prod_le_iff.mpr
    constructor <;> simp only [norm_mul,norm_neg,Complex.norm_I,one_mul]
    · exact (mul_le_mul_of_nonneg_left ((norm_fst_le _).trans (hF t)) (norm_nonneg _)).trans_eq (by ring)
    · exact (mul_le_mul_of_nonneg_left ((norm_snd_le _).trans (hF t)) (norm_nonneg _)).trans_eq (by ring)
  have hobs (u : ℂ × ℂ) : ‖L u‖ ≤ ‖u‖ :=
    (L.le_opNorm u).trans (by simpa using mul_le_mul_of_nonneg_right hL (norm_nonneg u))
  have hv (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖L (classicalSolution φ z v t-classicalFreeVector w v t)‖ ≤
        (Real.exp (‖z‖+M)+Real.exp ‖w‖)*‖v‖ :=
    (hobs _).trans ((norm_sub_le _ _).trans ((add_le_add (hS ⟨t,ht⟩) (hF ⟨t,ht⟩)).trans_eq (by ring)))
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖deriv (fun s => L (classicalSolution φ z v s-classicalFreeVector w v s)) t‖ ≤
        ((‖z‖+M)*Real.exp (‖z‖+M)+‖w‖*Real.exp ‖w‖)*‖v‖ := by
    have he : deriv (fun s => L (classicalSolution φ z v s-classicalFreeVector w v s)) t =
        L (deriv (classicalSolution φ z v) t-deriv (classicalFreeVector w v) t) :=
      (L.hasFDerivAt.comp_hasDerivAt t
        (((contDiff_one_iff_deriv.mp (contDiff_classicalSolution φ z v)).1 t).hasDerivAt.sub
          ((contDiff_one_iff_deriv.mp (contDiff_classicalFreeVector w v)).1 t).hasDerivAt)).deriv
    rw [he]
    exact (hobs _).trans ((norm_sub_le _ _).trans
      ((add_le_add (hdS ⟨t,ht⟩) (hdF ⟨t,ht⟩)).trans_eq (by ring)))
  exact (norm_unitIntervalC1Coefficients_le hq _ _
    ((Real.exp (‖z‖+M)+Real.exp ‖w‖)*‖v‖)
    (((‖z‖+M)*Real.exp (‖z‖+M)+‖w‖*Real.exp ‖w‖)*‖v‖)
    (by positivity) (by positivity) hv hd).trans_eq (by unfold classicalFourierReferenceBound; ring)

end NLS.ZakharovShabat
