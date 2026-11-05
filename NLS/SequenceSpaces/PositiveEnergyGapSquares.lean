import NLS.SequenceSpaces.PositiveEnergyMidpoints

/-! # Native ell1 normalized energy gap squares from symmetric frequency data -/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal
namespace NLS.Coeff

def positiveEnergyGapSquares (d : Coeff 2) (g : Coeff 1) : Coeff 1 :=
  let a := exponentInclusion (show (2 : ENNReal) ≤ ⊤ from le_top)
    (multiplierCLM positiveIndexReciprocal d)
  let b := holderProduct (p := ⊤) (r := 1) (q := 1) a g
  positiveDeletedProjection 1 0
    ((4*(Real.pi : ℂ)^2) • g+(8*(Real.pi : ℂ)) • b+
      (4 : ℂ) • holderProduct (p := ⊤) (r := 1) (q := 1) a b)

theorem analyticOnNhd_positiveEnergyGapSquares :
    AnalyticOnNhd ℂ (fun t : Coeff 2 × Coeff 1 => positiveEnergyGapSquares t.1 t.2) univ := by
  intro t _
  let R : Coeff 2 →L[ℂ] Coeff ⊤ :=
    (exponentInclusion (show (2 : ENNReal) ≤ ⊤ from le_top)).comp
      (multiplierCLM positiveIndexReciprocal)
  let B : Coeff ⊤ →L[ℂ] Coeff 1 →L[ℂ] Coeff 1 := holderProduct
  let a : Coeff 2 × Coeff 1 → Coeff ⊤ := fun x => R x.1
  let b : Coeff 2 × Coeff 1 → Coeff 1 := fun x => B (a x) x.2
  have ha : AnalyticAt ℂ a t := (R.analyticAt t.1).comp analyticAt_fst
  have hb : AnalyticAt ℂ b t := (B.analyticAt_bilinear _).comp₂ ha analyticAt_snd
  have hbb : AnalyticAt ℂ (fun x => B (a x) (b x)) t :=
    (B.analyticAt_bilinear _).comp₂ ha hb
  let L₁ : (Coeff 2 × Coeff 1) →L[ℂ] Coeff 1 :=
    (4*(Real.pi : ℂ)^2) • ContinuousLinearMap.snd ℂ (Coeff 2) (Coeff 1)
  let L₂ : Coeff 1 →L[ℂ] Coeff 1 := (8*(Real.pi : ℂ)) • ContinuousLinearMap.id ℂ (Coeff 1)
  let L₃ : Coeff 1 →L[ℂ] Coeff 1 := (4 : ℂ) • ContinuousLinearMap.id ℂ (Coeff 1)
  have h₁ : AnalyticAt ℂ (fun x => L₁ x) t := L₁.analyticAt t
  have h₂ : AnalyticAt ℂ (fun x => L₂ (b x)) t := (L₂.analyticAt _).comp (f := b) hb
  have h₃ : AnalyticAt ℂ (fun x => L₃ (B (a x) (b x))) t :=
    (L₃.analyticAt _).comp (f := fun x => B (a x) (b x)) hbb
  have hi := (h₁.add h₂).add h₃
  exact ((positiveDeletedProjection 1 0).analyticAt _).comp
    (f := fun x => L₁ x+L₂ (b x)+L₃ (B (a x) (b x))) hi

theorem positiveEnergyGapSquares_positive (d : Coeff 2) (g : Coeff 1) (n : ℕ+) :
    positiveEnergyGapSquares d g (n : ℤ) =
      (2*(Real.pi : ℂ)+2*d (n : ℤ)/(n : ℂ))^2*g (n : ℤ) := by
  have hn : (0 : ℤ) < (n : ℤ) := by exact_mod_cast n.property
  simp only [positiveEnergyGapSquares,positiveDeletedProjection_apply,
    if_pos (show 0 < (n : ℤ) ∧ (n : ℤ) ≠ 0 from ⟨hn,ne_of_gt hn⟩),
    lp.coeFn_add,Pi.add_apply,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,
    holderProduct_apply,exponentInclusion_apply,multiplierCLM_apply,multiplier_apply,
    positiveIndexReciprocal_apply,positiveIndexWeight,if_pos hn,Int.cast_natCast]
  ring

theorem positiveEnergyGapSquares_nonpositive (d : Coeff 2) (g : Coeff 1)
    (j : ℤ) (hj : j ≤ 0) : positiveEnergyGapSquares d g j = 0 := by
  simp only [positiveEnergyGapSquares,positiveDeletedProjection_apply,
    if_neg (show ¬(0 < j ∧ j ≠ 0) from fun h => (not_lt.mpr hj) h.1)]

end NLS.Coeff
