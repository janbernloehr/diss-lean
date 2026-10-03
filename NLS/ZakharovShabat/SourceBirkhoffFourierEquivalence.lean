import NLS.ZakharovShabat.SourceBirkhoffFourier

/-! # The free Birkhoff Fourier transform as a Banach-space isomorphism

The inverse restores the reflected first source component and the
unreflected second component, with the exact square-root normalization.
-/

noncomputable section
open Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The explicit bounded inverse of the source Fourier transform. -/
def sourceBirkhoffFourierInverse : (Coeff p × Coeff p) →L[ℂ] CoeffPair p :=
  let x := ContinuousLinearMap.fst ℂ (Coeff p) (Coeff p)
  let y := ContinuousLinearMap.snd ℂ (Coeff p) (Coeff p)
  let a := Coeff.reflection.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (((-1 : ℂ)/(Real.sqrt 2 : ℂ)) • (x-I • y))
  let b := ((-1 : ℂ)/(Real.sqrt 2 : ℂ)) • (x+I • y)
  (CoeffPair.toMax p).symm.toContinuousLinearMap.comp (a.prod b)

@[simp] theorem sourceBirkhoffFourierInverse_fst (v : Coeff p × Coeff p) (n : ℤ) :
    (sourceBirkhoffFourierInverse v).fst n = -(v.1 (-n)-I*v.2 (-n))/(Real.sqrt 2 : ℂ) := by
  change (Coeff.reflection (((-1 : ℂ)/(Real.sqrt 2 : ℂ)) • (v.1-I • v.2))) n = _
  simp only [Coeff.reflection_apply,lp.coeFn_smul,lp.coeFn_sub,Pi.smul_apply,Pi.sub_apply,smul_eq_mul]
  ring

@[simp] theorem sourceBirkhoffFourierInverse_snd (v : Coeff p × Coeff p) (n : ℤ) :
    (sourceBirkhoffFourierInverse v).snd n = -(v.1 n+I*v.2 n)/(Real.sqrt 2 : ℂ) := by
  change (((-1 : ℂ)/(Real.sqrt 2 : ℂ)) • (v.1+I • v.2)) n = _
  simp only [lp.coeFn_smul,lp.coeFn_add,Pi.smul_apply,Pi.add_apply,smul_eq_mul]
  ring

private theorem sqrt_two_complex_sq : (Real.sqrt 2 : ℂ)^2 = 2 := by
  norm_cast
  exact Real.sq_sqrt (by norm_num)

/-- The inverse recovers the entire source, including the reflected index. -/
@[simp] theorem sourceBirkhoffFourierInverse_fourier (h : CoeffPair p) :
    sourceBirkhoffFourierInverse (sourceBirkhoffFourier h) = h := by
  have hs : (Real.sqrt 2 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (by norm_num)))
  apply (CoeffPair.toMax p).injective
  apply Prod.ext
  · ext n
    change (sourceBirkhoffFourierInverse (sourceBirkhoffFourier h)).fst n = h.fst n
    simp only [sourceBirkhoffFourierInverse_fst,sourceBirkhoffFourier_fst,sourceBirkhoffFourier_snd,neg_neg]
    field_simp
    simp only [sqrt_two_complex_sq]
    ring
  · ext n
    change (sourceBirkhoffFourierInverse (sourceBirkhoffFourier h)).snd n = h.snd n
    simp only [sourceBirkhoffFourierInverse_snd,sourceBirkhoffFourier_fst,sourceBirkhoffFourier_snd]
    field_simp
    simp only [sqrt_two_complex_sq]
    ring

/-- The Fourier transform recovers every output pair from the explicit inverse. -/
@[simp] theorem sourceBirkhoffFourier_fourierInverse (v : Coeff p × Coeff p) :
    sourceBirkhoffFourier (sourceBirkhoffFourierInverse v) = v := by
  have hs : (Real.sqrt 2 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (by norm_num)))
  apply Prod.ext <;> ext n <;>
    simp only [sourceBirkhoffFourier_fst,sourceBirkhoffFourier_snd,
      sourceBirkhoffFourierInverse_fst,sourceBirkhoffFourierInverse_snd,neg_neg]
  all_goals field_simp; simp only [sqrt_two_complex_sq]; ring

/-- The free source Fourier map is a bounded complex-linear equivalence. -/
def sourceBirkhoffFourierEquiv : CoeffPair p ≃L[ℂ] (Coeff p × Coeff p) where
  toLinearEquiv := {
    toFun := sourceBirkhoffFourier
    invFun := sourceBirkhoffFourierInverse
    left_inv := sourceBirkhoffFourierInverse_fourier
    right_inv := sourceBirkhoffFourier_fourierInverse
    map_add' := sourceBirkhoffFourier.map_add
    map_smul' := sourceBirkhoffFourier.map_smul }
  continuous_toFun := sourceBirkhoffFourier.continuous
  continuous_invFun := sourceBirkhoffFourierInverse.continuous

@[simp] theorem sourceBirkhoffFourierEquiv_apply (h : CoeffPair p) :
    sourceBirkhoffFourierEquiv h = sourceBirkhoffFourier h := rfl

@[simp] theorem sourceBirkhoffFourierEquiv_symm_apply (v : Coeff p × Coeff p) :
    sourceBirkhoffFourierEquiv.symm v = sourceBirkhoffFourierInverse v := rfl

end NLS.ZakharovShabat
