import NLS.ZakharovShabat.ExponentOperatorCompatibility

/-!
# Recovering the smaller-exponent domain from a pencil equation

A domain vector at any finite exponent has absolutely summable coefficients.
Multiplication by a smaller-exponent potential therefore belongs to that
smaller base space. The pencil equation then recovers the derivative there.
-/

noncomputable section
open Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- The first raw coordinate of the actual spectral pencil. -/
theorem spectralPencil_fst_apply (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ) (a : Domain p) (n : ℤ) :
    (spectralPencil hp φ z a).1 n = z*a.1.val n -
      (-(Real.pi : ℂ)*n*a.1.val n + ∑' k : ℤ, φ.1 (n-k)*a.2.val k) := by
  change z*(scalarInclusion a.1 n) - (operator hp φ a).1 n = _
  rw [scalarInclusion_apply, operator_fst_apply]

/-- The second coordinate retains the opposite free derivative sign. -/
theorem spectralPencil_snd_apply (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ) (a : Domain p) (n : ℤ) :
    (spectralPencil hp φ z a).2 n = z*a.2.val n -
      ((Real.pi : ℂ)*n*a.2.val n + ∑' k : ℤ, φ.2 (n-k)*a.1.val k) := by
  change z*(scalarInclusion a.2 n) - (operator hp φ a).2 n = _
  rw [scalarInclusion_apply, operator_snd_apply]

/-- If the potential and source belong to the smaller exponent, so does the full domain vector. -/
theorem exists_domain_of_spectralPencil_exponent (hq : q ≠ ⊤) (h : p ≤ q)
    (φ b : PairSpace p) (z : ℂ) (a : Domain q)
    (he : spectralPencil hq (pairExponentInclusion h φ) z a = pairExponentInclusion h b) :
    ∃ c : Domain p, domainExponentInclusion h c = a := by
  let v₁ := WeightedCoeff.sobolevToL1CLM q hq a.1
  let v₂ := WeightedCoeff.sobolevToL1CLM q hq a.2
  let u₁ := Coeff.exponentInclusion (show (1 : ENNReal) ≤ p from Fact.out) v₁
  let u₂ := Coeff.exponentInclusion (show (1 : ENNReal) ≤ p from Fact.out) v₂
  let d₁ : Coeff p := I • (b.1-z • u₁+Coeff.convolution φ.1 v₂)
  let d₂ : Coeff p := -I • (b.2-z • u₂+Coeff.convolution φ.2 v₁)
  have he₁ (n : ℤ) := congrArg (fun x : PairSpace q => x.1 n) he
  have he₂ (n : ℤ) := congrArg (fun x : PairSpace q => x.2 n) he
  simp only [spectralPencil_fst_apply, pairExponentInclusion_apply, Coeff.exponentInclusion_apply] at he₁
  simp only [spectralPencil_snd_apply, pairExponentInclusion_apply, Coeff.exponentInclusion_apply] at he₂
  have hd₁ (n : ℤ) : I*(Real.pi : ℂ)*n*a.1.val n = d₁ n := by
    simp only [d₁, lp.coeFn_smul, lp.coeFn_add, lp.coeFn_sub, Pi.smul_apply,
      Pi.add_apply, Pi.sub_apply, smul_eq_mul, u₁, v₁, v₂,
      Coeff.exponentInclusion_apply, WeightedCoeff.sobolevToL1CLM_apply, Coeff.convolution_apply]
    linear_combination I * he₁ n
  have hd₂ (n : ℤ) : I*(Real.pi : ℂ)*n*a.2.val n = d₂ n := by
    simp only [d₂, lp.coeFn_smul, lp.coeFn_add, lp.coeFn_sub, Pi.smul_apply,
      Pi.add_apply, Pi.sub_apply, smul_eq_mul, u₂, v₁, v₂,
      Coeff.exponentInclusion_apply, WeightedCoeff.sobolevToL1CLM_apply, Coeff.convolution_apply]
    linear_combination -I * he₂ n
  have hu₁ : Memℓp (fun n => a.1.val n) p := by
    have hu : Memℓp (fun n => u₁ n) p := lp.memℓp u₁
    simpa only [u₁, v₁, Coeff.exponentInclusion_apply, WeightedCoeff.sobolevToL1CLM_apply] using hu
  have hu₂ : Memℓp (fun n => a.2.val n) p := by
    have hu : Memℓp (fun n => u₂ n) p := lp.memℓp u₂
    simpa only [u₂, v₂, Coeff.exponentInclusion_apply, WeightedCoeff.sobolevToL1CLM_apply] using hu
  have hder₁ : Memℓp (fun n => I*(Real.pi : ℂ)*n*a.1.val n) p := by
    simpa only [hd₁] using lp.memℓp d₁
  have hder₂ : Memℓp (fun n => I*(Real.pi : ℂ)*n*a.2.val n) p := by
    simpa only [hd₂] using lp.memℓp d₂
  let c : Domain p :=
    (⟨a.1.val, memlp_sobolev_weight_of_derivative hu₁ hder₁⟩,
     ⟨a.2.val, memlp_sobolev_weight_of_derivative hu₂ hder₂⟩)
  refine ⟨c, ?_⟩
  apply Prod.ext
  · apply Subtype.ext
    funext n
    exact WeightedCoeff.exponentInclusion_apply _ h c.1 n
  · apply Subtype.ext
    funext n
    exact WeightedCoeff.exponentInclusion_apply _ h c.2 n

end NLS.ZakharovShabat
