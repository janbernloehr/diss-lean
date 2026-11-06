import NLS.SequenceSpaces.WeightedScalarActionFamilyDescent

/-! # Zero fibers, scalar homogeneity and real lifts of normalized weighted actions -/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal
namespace NLS.WeightedCoeff

theorem actionsFromNormalizedCoordinates_smul (w : Weight) (z : Coeff 2 × Coeff 2) (c : ℂ) :
    actionsFromNormalizedCoordinates w (c • z)=c^2 • actionsFromNormalizedCoordinates w z := by
  apply Subtype.ext
  funext k
  simp only [actionsFromNormalizedCoordinates_apply,smul_val,Prod.smul_fst,Prod.smul_snd,
    lp.coeFn_smul,Pi.smul_apply,smul_eq_mul]
  ring

theorem eq_zero_of_real_actionsFromNormalizedCoordinates_eq_zero
    (w : Weight) (z : Coeff 2 × Coeff 2) (hz : z ∈ Coeff.realPairLocus 2)
    (ha : actionsFromNormalizedCoordinates w z=0) : z=0 := by
  have hcoords (k : ℤ) : z.1 k=0 ∧ z.2 k=0 := by
    have he := congrArg (fun b : WeightedCoeff w 1 => b.val k) ha
    simp only [actionsFromNormalizedCoordinates_apply,zero_val] at he
    have hden : (2 : ℂ)*(w k : ℂ) ≠ 0 := mul_ne_zero (by norm_num) (w.complex_ne_zero k)
    have hxy : z.1 k^2+z.2 k^2=0 := (div_eq_zero_iff.mp he).resolve_right hden
    have hr : (z.1 k).re^2+(z.2 k).re^2=0 := by
      have hh := congrArg Complex.re hxy
      simpa only [add_re,pow_two,mul_re,(hz.1 k),(hz.2 k),zero_mul,sub_zero,zero_re] using hh
    have hx : (z.1 k).re=0 := by nlinarith [sq_nonneg (z.2 k).re]
    have hy : (z.2 k).re=0 := by nlinarith [sq_nonneg (z.1 k).re]
    exact ⟨Complex.ext hx (hz.1 k),Complex.ext hy (hz.2 k)⟩
  apply Prod.ext
  · ext k
    exact (hcoords k).1
  · ext k
    exact (hcoords k).2

theorem exists_real_actionsFromNormalizedCoordinates_lift
    (w : Weight) (b : WeightedCoeff w 1) (hb : b ∈ nonnegativeLocus w 1) :
    ∃ z : Coeff 2 × Coeff 2, z ∈ Coeff.realPairLocus 2 ∧ actionsFromNormalizedCoordinates w z=b := by
  obtain ⟨z,hzr,hza,_⟩ := Coeff.exists_real_quadraticActions_lift (p := 2)
    (by norm_num) ((weightIsometry w 1) b) ((mem_nonnegativeLocus_iff w 1 b).mp hb)
  refine ⟨z,hzr,?_⟩
  apply (weightIsometry w 1).injective
  rw [weight_actionsFromNormalizedCoordinates,hza]

end NLS.WeightedCoeff
