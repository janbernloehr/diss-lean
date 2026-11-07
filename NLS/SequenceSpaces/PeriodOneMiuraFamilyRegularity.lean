import NLS.SequenceSpaces.PeriodOneMiuraFiniteRegularity
import NLS.SequenceSpaces.YoungConvolution

/-!
# Norm-continuous finite-p realizations of rough Miura families

The derivative uses the continuous stronger Sobolev realization. The
quadratic term uses the original L2 topology and the continuous Young
convolution into bounded coefficients. The strict negative-weight threshold
then supplies a continuous finite-p potential image with exact raw values.
-/
noncomputable section
open Complex
open scoped ENNReal
namespace NLS
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A continuous L2 family with a continuous realization at order 1-b
has a continuous shifted Miura realization at order -b in finite p,
provided b*p>1. Both maps represent the same entire unit-period sequence. -/
theorem exists_continuous_periodOneMiura_finiteP_family
    (hp : p ≠ ⊤) (b : ℝ) (hbp : 1 < b*p.toReal)
    {T : Type*} [TopologicalSpace T] (u : T → Coeff 2) (hu : Continuous u)
    (F : T → Coeff p) (hF : Continuous F)
    (hFc : ∀ x n, F x n = (Weight.sobolev (1-b) n:ℂ)*u x n) (c : ℂ) :
    ∃ G : T → WeightedCoeff (Weight.sobolev (-b)) p, Continuous G ∧
      ∀ x n, (G x).val n =
        (periodOneMiura (u x)-periodOneL2Inclusion (lp.single 2 0 c)).val n := by
  have hpR : 0 < p.toReal := ENNReal.toReal_pos
    (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hp
  have hw : Memℓp (fun n : ℤ => (Weight.sobolev (-b) n:ℂ)) p := by
    convert Weight.inverse_sobolev_memlp hpR hbp using 1
    funext n
    simp only [Weight.sobolev_apply,Real.rpow_neg (by positivity : 0 ≤ 1+|(n:ℝ)|),
      Complex.ofReal_inv]
  let w : Coeff p := ⟨_,hw⟩
  let A := fun x => (WeightedCoeff.weightIsometry (Weight.sobolev (-b+1)) p).symm (F x)
  have hA : Continuous A := (WeightedCoeff.weightIsometry _ p).symm.continuous.comp hF
  have hAc (x : T) (n : ℤ) : (A x).val n = u x n := by
    change F x n/(Weight.sobolev (-b+1) n:ℂ) = u x n
    rw [hFc,show -b+1 = 1-b by ring]
    exact mul_div_cancel_left₀ _ ((Weight.sobolev (1-b)).complex_ne_zero n)
  let Q := fun x => (WeightedCoeff.weightIsometry (Weight.sobolev (-b)) p).symm
    (Coeff.holderProduct (q := p) w (Coeff.youngConvolution youngRelation_two_two_top (u x) (u x)))
  have hY : Continuous (fun x => Coeff.youngConvolution youngRelation_two_two_top (u x) (u x)) :=
    (Coeff.continuous_youngConvolution youngRelation_two_two_top).comp (hu.prodMk hu)
  have hQ : Continuous Q := (WeightedCoeff.weightIsometry _ p).symm.continuous.comp
    ((Coeff.holderProduct (p := p) (r := ⊤) (q := p) w).continuous.comp hY)
  have hQc (x : T) (n : ℤ) : (Q x).val n = ∑' j : ℤ, u x (n-j)*u x j := by
    change ((Weight.sobolev (-b) n:ℂ)*(Coeff.youngConvolution youngRelation_two_two_top (u x) (u x) n))/
      (Weight.sobolev (-b) n:ℂ) = _
    rw [mul_div_cancel_left₀ _ ((Weight.sobolev (-b)).complex_ne_zero n),Coeff.youngConvolution_apply]
  let k := (WeightedCoeff.weightIsometry (Weight.sobolev (-b)) p).symm (lp.single p 0 c)
  have hkc (n : ℤ) : k.val n = (periodOneL2Inclusion (lp.single 2 0 c)).val n := by
    rw [periodOneL2Inclusion_apply]
    change (lp.single p 0 c : Coeff p) n/(Weight.sobolev (-b) n:ℂ) =
      (lp.single 2 0 c : Coeff 2) n
    by_cases hn : n = 0
    · subst n
      simp [Weight.sobolev_apply]
    · simp [lp.single_apply,hn]
  let G := fun x => (2:ℂ) • WeightedCoeff.sobolevDerivative (-b) (A x)+Q x-k
  have hG : Continuous G := by
    change Continuous (fun x => (2:ℂ) • WeightedCoeff.sobolevDerivative (-b) (A x)+Q x-k)
    exact (((continuous_const : Continuous (fun _ : T => (2:ℂ))).smul
      ((WeightedCoeff.sobolevDerivative (-b)).continuous.comp hA)).add hQ).sub
        (continuous_const : Continuous (fun _ : T => k))
  refine ⟨G,hG,?_⟩
  intro x n
  change (2:ℂ)*(WeightedCoeff.sobolevDerivative (-b) (A x)).val n+(Q x).val n-k.val n = _
  rw [WeightedCoeff.sobolevDerivative_apply,hAc,hQc,hkc,WeightedCoeff.sub_val,periodOneMiura_apply]
  ring

end NLS
