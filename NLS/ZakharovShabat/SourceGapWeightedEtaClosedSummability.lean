import NLS.ZakharovShabat.SourceGapWeightedEtaFiniteGapDifferential
import NLS.ZakharovShabat.SourceGapWeightedEtaFreeCotangent
import NLS.ZakharovShabat.SourceSpectralGradientSobolevSummability
import NLS.ZakharovShabat.SourceAntiDiscriminantSobolevSummability
import NLS.ZakharovShabat.SourceAntiDiscriminantDiscLp
import NLS.SequenceSpaces.BoundedScalarProducts

/-! # Summability of the closed-gap differential error

The exact spectral expression splits into the two G.7 errors and three
anti-discriminant corrections. Bounded inverse omitted products and the
signed free normalization make every correction an ℓp operator sequence.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Exact decomposition around the signed free Fourier functional. -/
theorem sourceGapWeightedEtaClosedCotangent_sub_free
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) (n : ℤ) (sign : ℂ) :
    let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ n
    let dμ := fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n) φ
    let dτ := fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodicMidpoint hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) n) φ
    let A := sourceAntiDiscriminantCotangent hp hp1 μ φ
    let A₀ := sourceAntiDiscriminantCotangent hp hp1 ((Real.pi : ℂ)*n) 0
    let B := (sourceStandardRootOmittedProduct hp hp1 n φ μ)⁻¹
    sourceGapWeightedEtaClosedCotangent hp hp1 n sign φ-sourceGapWeightedEtaFreeCotangent hp hp1 n sign =
      (-2 : ℂ) • (dμ-sourceFreeDirichletCotangent p n)+(2 : ℂ) • dτ-
        (sign*I) • (B • (A-A₀)+(B-cos ((Real.pi : ℂ)*n)) • A₀+
          B • (deriv (sourceAntiDiscriminantCandidate hp hp1 φ) μ • dμ)) := by
  dsimp only
  ext h
  simp only [sourceGapWeightedEtaClosedCotangent,sourceGapWeightedEtaFreeCotangent,
    sub_apply,add_apply,smul_apply,smul_eq_mul,div_eq_mul_inv,mul_inv_rev]
  ring

/-- On every real H¹ source, the closed-gap expression differs from its
signed free Fourier functional by an outer ℓp sequence of actual operators. -/
theorem memlp_sourceGapWeightedEtaClosedCotangent_sub_free
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (φ : CoeffPair 2) (hφ : IsRealType (CoeffPair.toMax 2 φ))
    (a : Domain 2) (ha : periodOnePotential φ = domainInclusion a) (sign : ℂ) :
    Memℓp (fun n : ℤ => sourceGapWeightedEtaClosedCotangent hp hp1 n sign
      (CoeffPair.exponentInclusion h2p φ)-sourceGapWeightedEtaFreeCotangent hp hp1 n sign) p := by
  let ψ := CoeffPair.exponentInclusion h2p φ
  have hψ : IsRealType (CoeffPair.toMax p ψ) := fun n => hφ n
  let μ (n : ℤ) := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n
  let dμ (n : ℤ) := fderiv ℂ (fun χ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet χ n) ψ
  let dτ (n : ℤ) := fderiv ℂ (fun χ : CoeffPair p => canonicalPeriodicMidpoint hp hp1
    (periodOnePotential χ) (periodOnePotential_mem χ) n) ψ
  let A (n : ℤ) := sourceAntiDiscriminantCotangent hp hp1 (μ n) ψ
  let A₀ (n : ℤ) := sourceAntiDiscriminantCotangent hp hp1 ((Real.pi : ℂ)*n) 0
  let B (n : ℤ) := (sourceStandardRootOmittedProduct hp hp1 n ψ (μ n))⁻¹
  let δ (n : ℤ) := deriv (sourceAntiDiscriminantCandidate hp hp1 ψ) (μ n)
  obtain ⟨W,_,hreal,hgrad⟩ := exists_global_source_spectral_gradients_sobolev_memlp hp hp1 h2p
  have hg := hgrad φ (hreal hψ) a ha
  have hmid : Memℓp dτ p := hg.1
  have hdir : Memℓp (fun n => dμ n-sourceFreeDirichletCotangent p n) p := hg.2
  have hanti : Memℓp (fun n => A n-A₀ n) p :=
    memlp_source_antiDiscriminantCotangent_boundary_error hp hp1 h2p φ a ha .dirichlet
  have hinv : Memℓp (fun n => B n-cos ((Real.pi : ℂ)*n)) p :=
    memlp_sourceStandardRootOmittedProduct_boundary_inv_sub_free hp hp1 .dirichlet ψ hψ
  have hδ : Memℓp δ p := (memℓp_sourceAntiDiscriminant_at_dirichletRoots hp hp1 ψ).2
  obtain ⟨C,_,hC⟩ := exists_bound_sourceStandardRootOmittedProduct_boundary_inv hp hp1 .dirichlet ψ hψ
  obtain ⟨M,_,hM⟩ := exists_norm_bound_of_memlp hdir
  have hdμ (n : ℤ) : ‖dμ n‖ ≤ M+1 := by
    calc
      ‖dμ n‖ = ‖(dμ n-sourceFreeDirichletCotangent p n)+sourceFreeDirichletCotangent p n‖ := by rw [sub_add_cancel]
      _ ≤ ‖dμ n-sourceFreeDirichletCotangent p n‖+‖sourceFreeDirichletCotangent p n‖ := norm_add_le _ _
      _ ≤ M+1 := add_le_add (hM n) (norm_sourceFreeDirichletCotangent_le n)
  have h₁ := memlp_smul_of_bounded_scalar B _ hanti C hC
  have h₂ := memlp_smul_of_bounded_vector _ A₀ hinv 2 (norm_sourceAntiDiscriminantCotangent_zero_le hp hp1)
  have h₃ := memlp_smul_of_bounded_scalar B _
    (memlp_smul_of_bounded_vector δ dμ hδ (M+1) hdμ) C hC
  have hsum := ((hdir.const_smul (-2 : ℂ)).add (hmid.const_smul (2 : ℂ))).sub
    (((h₁.add h₂).add h₃).const_smul (sign*I))
  convert hsum using 1
  funext n
  exact sourceGapWeightedEtaClosedCotangent_sub_free hp hp1 ψ n sign

end NLS.ZakharovShabat
