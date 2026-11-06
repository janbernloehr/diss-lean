import NLS.SequenceSpaces.PeriodOneMiuraSobolevEquivalence

/-! # Exact weighted coefficient algebra for the actual shifted Miura equation -/
noncomputable section
set_option autoImplicit false
open Complex
open scoped ENNReal
namespace NLS

theorem memlp_sobolev_single_zero (p : ℝ≥0∞) (s : ℝ) (c : ℂ) :
    Memℓp (fun n => (Weight.sobolev s n : ℂ)*(lp.single 2 0 c : Coeff 2) n) p := by
  have h := (WeightedCoeff.ofFinsupp (Weight.sobolev s) p (Finsupp.single 0 c)).property
  change Memℓp (fun n => (Weight.sobolev s n : ℂ)*
    (WeightedCoeff.ofFinsupp (Weight.sobolev s) p (Finsupp.single 0 c)).val n) p at h
  simpa only [WeightedCoeff.ofFinsupp_apply,lp.single_apply,Pi.single_apply,Finsupp.single_apply,
    show ∀ n : ℤ, (0=n ↔ n=0) from fun _ => eq_comm] using h

theorem memlp_sobolev_derivative_of_succ {p : ℝ≥0∞} [Fact (1≤p)] (s : ℝ)
    {u : ℤ → ℂ} (hu : Memℓp (fun n => (Weight.sobolev (s+1) n : ℂ)*u n) p) :
    Memℓp (fun n => (Weight.sobolev s n : ℂ)*(I*(Real.pi : ℂ)*n*u n)) p := by
  let a : WeightedCoeff (Weight.sobolev (s+1)) p := ⟨u,hu⟩
  have h := (WeightedCoeff.sobolevDerivative s a).property
  change Memℓp (fun n => (Weight.sobolev s n : ℂ)*(WeightedCoeff.sobolevDerivative s a).val n) p at h
  have he : (fun n => (Weight.sobolev s n : ℂ)*(WeightedCoeff.sobolevDerivative s a).val n) =
      (fun n => (Weight.sobolev s n : ℂ)*(I*(Real.pi : ℂ)*n*u n)) := by
    funext n
    exact congrArg (fun z : ℂ => (Weight.sobolev s n : ℂ)*z)
      (WeightedCoeff.sobolevDerivative_apply s a n)
  rw [he] at h
  exact h

/-- Solve for the derivative in the literal unit-period Miura equation.
The factor two in the period-two Sobolev derivative is retained exactly. -/
theorem periodOneMiura_lift_mem_of_weighted_image_and_product
    (p : ℝ≥0∞) (q : PeriodOneHminusOne) (u : Coeff 2) (c : ℂ)
    (himage : periodOneMiura u=q+periodOneL2Inclusion (lp.single 2 0 c)) (s : ℝ)
    (hq : Memℓp (fun n => (Weight.sobolev s n : ℂ)*q.val n) p)
    (hprod : Memℓp (fun n => (Weight.sobolev s n : ℂ)*(periodOneMiuraProduct u u).val n) p)
    (hu : Memℓp (fun n => (Weight.sobolev s n : ℂ)*u n) p) :
    Memℓp (fun n => (Weight.sobolev (s+1) n : ℂ)*u n) p := by
  have hder (n : ℤ) : I*(Real.pi : ℂ)*n*u n=
      (1/2 : ℂ)*(q.val n+(lp.single 2 0 c : Coeff 2) n-(periodOneMiuraProduct u u).val n) := by
    have he := congrArg (fun a : PeriodOneHminusOne => a.val n) himage
    rw [WeightedCoeff.add_val,periodOneMiura_apply,periodOneL2Inclusion_apply] at he
    rw [periodOneMiuraProduct_apply]
    linear_combination (1/2 : ℂ)*he
  have hd : Memℓp (fun n => (Weight.sobolev s n : ℂ)*(I*(Real.pi : ℂ)*n*u n)) p := by
    have heq : (fun n => (Weight.sobolev s n : ℂ)*(I*(Real.pi : ℂ)*n*u n))=
        (fun n => (1/2 : ℂ)*((Weight.sobolev s n : ℂ)*q.val n+
          (Weight.sobolev s n : ℂ)*(lp.single 2 0 c : Coeff 2) n-
          (Weight.sobolev s n : ℂ)*(periodOneMiuraProduct u u).val n)) := by
      funext n
      rw [hder]
      ring
    rw [heq]
    exact ((hq.add (memlp_sobolev_single_zero p s c)).sub hprod).const_mul (1/2 : ℂ)
  exact WeightedCoeff.memlp_sobolev_succ_of_derivative s hu hd

theorem periodOneMiura_image_mem_of_weighted_lift_and_product
    (p : ℝ≥0∞) [Fact (1≤p)] (q : PeriodOneHminusOne) (u : Coeff 2) (c : ℂ)
    (himage : periodOneMiura u=q+periodOneL2Inclusion (lp.single 2 0 c)) (s : ℝ)
    (hu : Memℓp (fun n => (Weight.sobolev (s+1) n : ℂ)*u n) p)
    (hprod : Memℓp (fun n => (Weight.sobolev s n : ℂ)*(periodOneMiuraProduct u u).val n) p) :
    Memℓp (fun n => (Weight.sobolev s n : ℂ)*q.val n) p := by
  have hder := memlp_sobolev_derivative_of_succ s hu
  have heq : (fun n => (Weight.sobolev s n : ℂ)*q.val n)=
      (fun n => (2 : ℂ)*((Weight.sobolev s n : ℂ)*(I*(Real.pi : ℂ)*n*u n))+
        (Weight.sobolev s n : ℂ)*(periodOneMiuraProduct u u).val n-
        (Weight.sobolev s n : ℂ)*(lp.single 2 0 c : Coeff 2) n) := by
    funext n
    have he := congrArg (fun a : PeriodOneHminusOne => a.val n) himage
    rw [WeightedCoeff.add_val,periodOneMiura_apply,periodOneL2Inclusion_apply] at he
    rw [periodOneMiuraProduct_apply]
    linear_combination -(Weight.sobolev s n : ℂ)*he
  rw [heq]
  exact ((hder.const_mul 2).add hprod).sub (memlp_sobolev_single_zero p s c)

end NLS
