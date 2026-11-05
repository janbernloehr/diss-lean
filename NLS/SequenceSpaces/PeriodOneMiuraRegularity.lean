import NLS.SequenceSpaces.PeriodOneMiuraQuadratic
import NLS.SequenceSpaces.BoundedScalarProducts

/-! # H1 regularity of L2 solutions of the distributional Miura equation

If v is L2 and v' + (m+1)v + v² is L2, then v is H1. The proof first
improves v to ell^(4/3), uses Young to put v² in L2, and recovers one
derivative. This is a coefficient proof in the original period-one
normalization, with no smoothness hypothesis on the solution.
-/
noncomputable section
set_option autoImplicit false
open Complex
open scoped ENNReal
namespace NLS

theorem memlp_periodOneMassInverseSymbol {p : ℝ≥0∞} (hp : 1 < p) (m : ℕ) :
    Memℓp (fun k => (periodOneMassSymbol m k)⁻¹) p := by
  apply ((Weight.inverse_sobolev_one_memlp hp).norm.const_mul (2 : ℝ)).mono
  intro k
  change ‖(periodOneMassSymbol m k)⁻¹‖ ≤ 2*‖(Weight.sobolev 1 k : ℂ)⁻¹‖
  have he : ‖(Weight.sobolev 1 k : ℂ)⁻¹‖ = (1+|(k : ℝ)|)⁻¹ :=
    norm_inverseBracketCoefficients_apply k
  rw [he]
  simpa only [div_eq_mul_inv] using norm_periodOneMassSymbol_inv_le_bracket m k

private abbrev pFourThirds : ℝ≥0∞ := ENNReal.ofReal (4/3 : ℝ)
private instance : Fact (1 ≤ pFourThirds) := ⟨by norm_num [pFourThirds]⟩

private theorem youngRelation_fourThirds : YoungRelation pFourThirds pFourThirds 2 := by
  unfold YoungRelation
  apply (ENNReal.toReal_eq_toReal_iff' (by simp) (by norm_num [pFourThirds])).mp
  rw [ENNReal.toReal_add (by simp) (by simp),
    ENNReal.toReal_add (by norm_num [pFourThirds]) (by norm_num [pFourThirds])]
  norm_num [pFourThirds]

theorem periodOneMiuraSolution_memlp_fourThirds (m : ℕ) (v q : Coeff 2)
    (hsolve : ∀ k, periodOneMassSymbol m k*v k+∑' j : ℤ, v (k-j)*v j = q k) :
    Memℓp (fun k => v k) (ENNReal.ofReal (4/3 : ℝ)) := by
  let c : Coeff ⊤ := Coeff.youngConvolution youngRelation_two_two_top v v
  have hleft : Memℓp (fun k => (periodOneMassSymbol m k)⁻¹*q k) pFourThirds :=
    (lp.memℓp (Coeff.holderProduct (q := 1) (periodOneMassKernel m) q)).of_exponent_ge
      (by norm_num [pFourThirds])
  have hright : Memℓp (fun k => (periodOneMassSymbol m k)⁻¹*c k) pFourThirds := by
    exact memlp_smul_of_bounded_vector _ _
      (memlp_periodOneMassInverseSymbol (by norm_num [pFourThirds]) m) ‖c‖
      (fun k => lp.norm_apply_le_norm (by simp) c k)
  convert hleft.sub hright using 1
  funext k
  change v k = (periodOneMassSymbol m k)⁻¹*q k-
    (periodOneMassSymbol m k)⁻¹*(∑' j : ℤ, v (k-j)*v j)
  rw [← hsolve k,mul_add,← mul_assoc,inv_mul_cancel₀ (periodOneMassSymbol_ne_zero m k)]
  simp

/-- Any L2 solution with an L2 image has one full Sobolev derivative. -/
theorem periodOneMiuraSolution_memlp_sobolev_one (m : ℕ) (v q : Coeff 2)
    (hsolve : ∀ k, periodOneMassSymbol m k*v k+∑' j : ℤ, v (k-j)*v j = q k) :
    Memℓp (fun k => (Weight.sobolev 1 k : ℂ)*v k) 2 := by
  let a : Coeff pFourThirds := ⟨v,periodOneMiuraSolution_memlp_fourThirds m v q hsolve⟩
  let b : Coeff 2 := Coeff.youngConvolution youngRelation_fourThirds a a
  have hb (k : ℤ) : b k = ∑' j : ℤ, v (k-j)*v j := rfl
  have hd : Memℓp (fun k => I*(Real.pi : ℂ)*k*v k) 2 := by
    have h := (lp.memℓp (q-(((m : ℝ)+1 : ℝ) : ℂ) • v-b)).const_mul (1/2 : ℂ)
    have he : (fun k => I*(Real.pi : ℂ)*k*v k) =
        (fun k => (1/2 : ℂ)*(q k-(((m : ℝ)+1 : ℝ) : ℂ)*v k-b k)) := by
      funext k
      rw [← hsolve k,hb,periodOneMassSymbol]
      ring
    rw [he]
    exact h
  exact ZakharovShabat.memlp_sobolev_weight_of_derivative (lp.memℓp v) hd

end NLS
