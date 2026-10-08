import NLS.SequenceSpaces.SobolevConvolution
import NLS.ZakharovShabat.Operator

/-! # A second derivative for eigenvectors of a one-derivative potential

The original operator equation and the convolution Leibniz rule recover
one additional derivative. No frequency cutoff or resolvent assumption
enters this regularity argument.
-/
noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The derivative of an original eigenvector itself has one derivative. -/
theorem exists_regular_derivative_of_eigenvector (hp : p ≠ ⊤) (a f : Domain p) (z : ℂ)
    (he : operator hp (domainInclusion a) f = z • domainInclusion f) :
    ∃ g : Domain p, (∀ n, derivative f.1 n = g.1.val n) ∧
      (∀ n, derivative f.2 n = g.2.val n) := by
  let g₁ : ScalarDomain p := Complex.I • (-z • f.1 + sobolevConvolution hp a.1 f.2)
  let g₂ : ScalarDomain p := -Complex.I • (-z • f.2 + sobolevConvolution hp a.2 f.1)
  refine ⟨(g₁,g₂), ?_, ?_⟩
  · intro n
    have h := congrArg (fun v : PairSpace p => v.1 n) he
    simp only [operator_fst_apply, domainInclusion_apply, Prod.smul_fst, lp.coeFn_smul,
      Pi.smul_apply, smul_eq_mul, scalarInclusion_apply] at h
    change Complex.I*(Real.pi:ℂ)*n*f.1.val n =
      Complex.I*((-z)*f.1.val n+(sobolevConvolution hp a.1 f.2).val n)
    rw [sobolevConvolution_apply]
    linear_combination -Complex.I*h
  · intro n
    have h := congrArg (fun v : PairSpace p => v.2 n) he
    simp only [operator_snd_apply, domainInclusion_apply, Prod.smul_snd, lp.coeFn_smul,
      Pi.smul_apply, smul_eq_mul, scalarInclusion_apply] at h
    change Complex.I*(Real.pi:ℂ)*n*f.2.val n =
      -Complex.I*((-z)*f.2.val n+(sobolevConvolution hp a.2 f.1).val n)
    rw [sobolevConvolution_apply]
    linear_combination Complex.I*h

/-- Both original eigenvector components have two weighted derivatives. -/
theorem eigenvector_memlp_sobolev_two (hp : p ≠ ⊤) (a f : Domain p) (z : ℂ)
    (he : operator hp (domainInclusion a) f = z • domainInclusion f) :
    Memℓp (fun n => (Weight.sobolev 2 n:ℂ)*f.1.val n) p ∧
    Memℓp (fun n => (Weight.sobolev 2 n:ℂ)*f.2.val n) p := by
  obtain ⟨g,h₁,h₂⟩ := exists_regular_derivative_of_eigenvector hp a f z he
  have hd₁ : Memℓp (fun n => (Weight.sobolev 1 n:ℂ)*(Complex.I*(Real.pi:ℂ)*n*f.1.val n)) p := by
    change Memℓp (fun n => (Weight.sobolev 1 n:ℂ)*derivative f.1 n) p
    simp only [h₁]
    exact g.1.property
  have hd₂ : Memℓp (fun n => (Weight.sobolev 1 n:ℂ)*(Complex.I*(Real.pi:ℂ)*n*f.2.val n)) p := by
    change Memℓp (fun n => (Weight.sobolev 1 n:ℂ)*derivative f.2 n) p
    simp only [h₂]
    exact g.2.property
  constructor
  · simpa only [one_add_one_eq_two] using WeightedCoeff.memlp_sobolev_succ_of_derivative 1 f.1.property hd₁
  · simpa only [one_add_one_eq_two] using WeightedCoeff.memlp_sobolev_succ_of_derivative 1 f.2.property hd₂

end NLS.ZakharovShabat
