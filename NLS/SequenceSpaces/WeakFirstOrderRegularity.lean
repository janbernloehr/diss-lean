import NLS.SequenceSpaces.PeriodOneMiuraRegularity
import NLS.SequenceSpaces.YoungConvolution
import NLS.ZakharovShabat.Operator

/-! Maximal-domain regularity for a rough scalar first-order equation.
The potential, solution and forcing start in the original period-two L2
coefficient space. The weak coefficient equation itself recovers H1. -/
noncomputable section
open Complex
open scoped ENNReal
namespace NLS

private abbrev fourThirds : ℝ≥0∞ := ENNReal.ofReal (4/3 : ℝ)
private instance : Fact (1 ≤ fourThirds) := ⟨by norm_num [fourThirds]⟩
private instance : Fact (1 ≤ (4:ℝ≥0∞)) := ⟨by norm_num⟩

private theorem young_two_fourThirds_four : YoungRelation 2 fourThirds 4 := by
  unfold YoungRelation
  apply (ENNReal.toReal_eq_toReal_iff' (by norm_num) (by norm_num [fourThirds])).mp
  rw [ENNReal.toReal_add (by norm_num) (by norm_num),
    ENNReal.toReal_add (by norm_num) (by norm_num [fourThirds])]
  norm_num [fourThirds]

private instance : fourThirds.HolderTriple 4 1 := by
  rw [ENNReal.holderTriple_iff]
  apply (ENNReal.toReal_eq_toReal_iff' (by norm_num [fourThirds]) (by norm_num)).mp
  rw [ENNReal.toReal_add (by norm_num [fourThirds]) (by norm_num)]
  norm_num [fourThirds]

/-- A weak first-order equation with L2 coefficient and forcing improves
an L2 solution to ell^(4/3), before any Sobolev regularity is assumed. -/
theorem weakFirstOrder_memlp_fourThirds (u v b : Coeff 2)
    (h : ∀ n : ℤ, I*(Real.pi : ℂ)*n*v n = (∑' k : ℤ, u (n-k)*v k)+b n) :
    Memℓp (fun n => v n) (ENNReal.ofReal (4/3 : ℝ)) := by
  let c : Coeff ⊤ := Coeff.youngConvolution youngRelation_two_two_top u v
  let r : Coeff 2 := v+(2:ℂ) • b
  have hleft : Memℓp (fun n => (periodOneMassSymbol 0 n)⁻¹*r n) fourThirds :=
    (lp.memℓp (Coeff.holderProduct (q := 1) (periodOneMassKernel 0) r)).of_exponent_ge
      (by norm_num [fourThirds])
  have hright : Memℓp (fun n => (periodOneMassSymbol 0 n)⁻¹*c n) fourThirds :=
    memlp_smul_of_bounded_vector _ _
      (memlp_periodOneMassInverseSymbol (by norm_num [fourThirds]) 0) ‖c‖
      (fun n => lp.norm_apply_le_norm (by simp) c n)
  have hm (n : ℤ) : periodOneMassSymbol 0 n*v n = r n+2*c n := by
    simp only [r, c, periodOneMassSymbol, Nat.cast_zero, zero_add, lp.coeFn_add,
      lp.coeFn_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Coeff.youngConvolution_apply, ofReal_one]
    linear_combination 2*h n
  convert hleft.add (hright.const_mul (2:ℂ)) using 1
  funext n
  change v n = (periodOneMassSymbol 0 n)⁻¹*r n+2*((periodOneMassSymbol 0 n)⁻¹*c n)
  calc
    v n = (periodOneMassSymbol 0 n)⁻¹*(periodOneMassSymbol 0 n*v n) := by
      rw [← mul_assoc, inv_mul_cancel₀ (periodOneMassSymbol_ne_zero 0 n), one_mul]
    _ = (periodOneMassSymbol 0 n)⁻¹*(r n+2*c n) := by rw [hm n]
    _ = _ := by ring


/-- The same weak equation yields absolute summability of its actual
solution coefficients, without an extra Wiener-space premise. -/
theorem weakFirstOrder_memlp_one (u v b : Coeff 2)
    (h : ∀ n : ℤ, I*(Real.pi : ℂ)*n*v n = (∑' k : ℤ, u (n-k)*v k)+b n) :
    Memℓp (fun n => v n) 1 := by
  let a : Coeff fourThirds := ⟨v, weakFirstOrder_memlp_fourThirds u v b h⟩
  let c : Coeff 4 := Coeff.youngConvolution young_two_fourThirds_four u a
  let r : Coeff 4 := Coeff.exponentInclusion (by norm_num : (2:ℝ≥0∞) ≤ 4) (v+(2:ℂ) • b)+(2:ℂ) • c
  let k : Coeff fourThirds := ⟨fun n => (periodOneMassSymbol 0 n)⁻¹,
    memlp_periodOneMassInverseSymbol (by norm_num [fourThirds]) 0⟩
  have hm (n : ℤ) : periodOneMassSymbol 0 n*v n = r n := by
    simp only [r, c, Coeff.exponentInclusion_apply, lp.coeFn_add, lp.coeFn_smul,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, Coeff.youngConvolution_apply, periodOneMassSymbol,
      Nat.cast_zero, zero_add, ofReal_one]
    change (1+2*I*(Real.pi:ℂ)*n)*v n = v n+2*b n+2*((∑' j : ℤ, u (n-j)*v j))
    linear_combination 2*h n
  convert lp.memℓp (Coeff.holderProduct (q := 1) k r) using 1
  funext n
  rw [Coeff.holderProduct_apply, ← hm n]
  change v n = (periodOneMassSymbol 0 n)⁻¹*(periodOneMassSymbol 0 n*v n)
  rw [← mul_assoc, inv_mul_cancel₀ (periodOneMassSymbol_ne_zero 0 n), one_mul]

/-- Every original L2 weak solution of v'=u*v+b with u,b in L2 belongs
to the full original H1 coefficient domain. No smoothness premise is added. -/
theorem weakFirstOrder_memlp_sobolev_one (u v b : Coeff 2)
    (h : ∀ n : ℤ, I*(Real.pi : ℂ)*n*v n = (∑' k : ℤ, u (n-k)*v k)+b n) :
    Memℓp (fun n => (Weight.sobolev 1 n : ℂ)*v n) 2 := by
  let a : Coeff 1 := ⟨v, weakFirstOrder_memlp_one u v b h⟩
  have hd : Memℓp (fun n => I*(Real.pi : ℂ)*n*v n) 2 := by
    have he : (fun n => I*(Real.pi : ℂ)*n*v n) = fun n => (Coeff.convolution u a+b) n := by
      funext n
      exact (h n).trans (by rw [lp.coeFn_add, Pi.add_apply, Coeff.convolution_apply])
    rw [he]
    exact lp.memℓp _
  exact ZakharovShabat.memlp_sobolev_weight_of_derivative (lp.memℓp v) hd

/-- The regular representative has precisely the same original raw coefficients. -/
def weakFirstOrderLift (u v b : Coeff 2)
    (h : ∀ n : ℤ, I*(Real.pi : ℂ)*n*v n = (∑' k : ℤ, u (n-k)*v k)+b n) :
    ZakharovShabat.ScalarDomain 2 :=
  ⟨v, weakFirstOrder_memlp_sobolev_one u v b h⟩

theorem scalarInclusion_weakFirstOrderLift (u v b : Coeff 2)
    (h : ∀ n : ℤ, I*(Real.pi : ℂ)*n*v n = (∑' k : ℤ, u (n-k)*v k)+b n) :
    ZakharovShabat.scalarInclusion (weakFirstOrderLift u v b h) = v := by
  ext n
  rw [ZakharovShabat.scalarInclusion_apply]
  rfl

/-- The constructed full-domain solution satisfies the actual bounded
domain-to-L2 differential operator equation. -/
theorem derivative_weakFirstOrderLift (u v b : Coeff 2)
    (h : ∀ n : ℤ, I*(Real.pi : ℂ)*n*v n = (∑' k : ℤ, u (n-k)*v k)+b n) :
    ZakharovShabat.derivative (weakFirstOrderLift u v b h) =
      ZakharovShabat.potentialMul (by norm_num) u (weakFirstOrderLift u v b h)+b := by
  ext n
  rw [ZakharovShabat.derivative_apply, lp.coeFn_add, Pi.add_apply,
    ZakharovShabat.potentialMul_apply]
  exact h n

end NLS
