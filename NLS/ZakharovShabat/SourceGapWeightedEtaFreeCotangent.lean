import NLS.ZakharovShabat.SourceFreeDirichletCotangent
import NLS.ZakharovShabat.SourceAntiDiscriminantGradientError
import NLS.ZakharovShabat.SourceOmittedProductBoundaryNormalization

/-! # The signed free eta functional and its uniform bounds -/

noncomputable section
open Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The exact free eta functional in the closed-gap spectral convention. -/
def sourceGapWeightedEtaFreeCotangent (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (sign : ℂ) :
    CoeffPair p →L[ℂ] ℂ :=
  (-2 : ℂ) • sourceFreeDirichletCotangent p n-
    (sign*I*cos ((Real.pi : ℂ)*n)) • sourceAntiDiscriminantCotangent hp hp1 ((Real.pi : ℂ)*n) 0

/-- The two signs select the original signed Fourier modes with factor minus two. -/
@[simp] theorem sourceGapWeightedEtaFreeCotangent_apply
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (sign : ℂ) (h : CoeffPair p) :
    sourceGapWeightedEtaFreeCotangent hp hp1 n sign h =
      (sign-1)*h.fst (-n)-(sign+1)*h.snd n := by
  have hc : (cos ((Real.pi : ℂ)*n))^2 = 1 := by
    rw [cos_freeCenter_eq_natAbs_sign,← pow_mul,mul_comm n.natAbs 2,pow_mul]
    norm_num
  simp only [sourceGapWeightedEtaFreeCotangent,sub_apply,smul_apply,smul_eq_mul,
    sourceFreeDirichletCotangent_apply,sourceAntiDiscriminantCotangent_zero_of_exponent]
  ring_nf
  simp only [I_sq,hc]
  ring

/-- The free Dirichlet functional has a uniform source operator bound. -/
theorem norm_sourceFreeDirichletCotangent_le (n : ℤ) :
    ‖sourceFreeDirichletCotangent p n‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro h
  have h₁ := (lp.norm_apply_le_norm (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' h.fst (-n)).trans
    (WithLp.norm_fst_le (Coeff p) h)
  have h₂ := (lp.norm_apply_le_norm (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' h.snd n).trans
    (WithLp.norm_snd_le (Coeff p) h)
  rw [sourceFreeDirichletCotangent_apply,norm_mul]
  norm_num
  have hb := norm_add_le (h.fst (-n)) (h.snd n)
  nlinarith

/-- The actual free anti-discriminant cotangents are uniformly bounded at all indices. -/
theorem norm_sourceAntiDiscriminantCotangent_zero_le
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) :
    ‖sourceAntiDiscriminantCotangent hp hp1 ((Real.pi : ℂ)*n) 0‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro h
  have h₁ := (lp.norm_apply_le_norm (zero_lt_one.trans hp1).ne' h.fst (-n)).trans (WithLp.norm_fst_le (Coeff p) h)
  have h₂ := (lp.norm_apply_le_norm (zero_lt_one.trans hp1).ne' h.snd n).trans (WithLp.norm_snd_le (Coeff p) h)
  rw [sourceAntiDiscriminantCotangent_zero_of_exponent,norm_mul,norm_mul,norm_I,norm_cos_freeCenter,one_mul,one_mul]
  exact (norm_sub_le _ _).trans (by linarith)

end NLS.ZakharovShabat
