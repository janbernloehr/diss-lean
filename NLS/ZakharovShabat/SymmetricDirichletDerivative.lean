import NLS.ZakharovShabat.SourceSpatialReflection
import NLS.ZakharovShabat.SourceBoundaryRootFloquetPoisson
import NLS.ZakharovShabat.SourceSpectralSequenceCompactDerivative
import NLS.ZakharovShabat.SourceFreeSpectralDifferentials
import NLS.Poisson.SourceHamiltonianDirection
import NLS.FunctionalAnalysis.CompactDenseRange
import NLS.SequenceSpaces.YoungFinite

/-! # The Dirichlet derivative on the symmetric complex slice

At every real reflection-fixed Hilbert source, the actual full Dirichlet
displacement derivative is an isomorphism on symmetric complex directions.
The root/Floquet logarithm brackets give preimages of every coordinate
vector, after reflection averaging. Compactness then upgrades dense range
to bijectivity. This is not an invertibility result for the signed-gap map.
-/
noncomputable section
open Set Complex NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Complex coordinates for reflection-fixed source directions. -/
def complexSymmetricSourceCoefficients (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Coeff p →L[ℂ] CoeffPair p :=
  (CoeffPair.toMax p).symm.toContinuousLinearMap.comp
    (Coeff.reflection.toContinuousLinearEquiv.toContinuousLinearMap.prod
      (ContinuousLinearMap.id ℂ (Coeff p)))

@[simp] theorem complexSymmetricSourceCoefficients_fst
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (a : Coeff p) (n : ℤ) :
    (complexSymmetricSourceCoefficients p a).fst n = a (-n) := rfl

@[simp] theorem complexSymmetricSourceCoefficients_snd
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (a : Coeff p) (n : ℤ) :
    (complexSymmetricSourceCoefficients p a).snd n = a n := rfl

/-- Averaging reflection supplies a symmetric direction with explicit coordinates. -/
theorem complexSymmetricSourceCoefficients_average
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (v : CoeffPair p) :
    complexSymmetricSourceCoefficients p
      (((1/2 : ℂ) • (v + sourceSpatialReflection v)).snd) =
        (1/2 : ℂ) • (v + sourceSpatialReflection v) := by
  apply (CoeffPair.toMax p).injective
  apply Prod.ext <;> ext n
  · change (1/2 : ℂ) * (v.snd (-n) + v.fst (-(-n))) =
      (1/2 : ℂ) * (v.fst n + v.snd (-n))
    rw [neg_neg, add_comm]
  · rfl

/-- At a reflection-fixed real source, each root cotangent is reflection invariant. -/
theorem fderiv_boundaryRoot_spatialReflection_of_fixed
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p)
    (b : BoundaryCondition) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (href : sourceSpatialReflection φ = φ)
    (n : ℤ) (v : CoeffPair p) :
    (fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 b ψ n) φ)
      (sourceSpatialReflection v) =
    (fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 b ψ n) φ) v := by
  let z := canonicalPeriodOneBoundaryRoots hp hp1 b φ n
  let C : CoeffPair p → ℂ := fun ψ => periodOneBoundaryCharacteristic hp hp1 b ψ z
  have hC := (analyticOnNhd_sourceBoundaryCharacteristic_section hp hp1 b z φ (mem_univ _)).differentiableAt.hasFDerivAt
  have hCR := (analyticOnNhd_sourceBoundaryCharacteristic_section hp hp1 b z
    (sourceSpatialReflection φ) (mem_univ _)).differentiableAt.hasFDerivAt
  have hcomp := hCR.comp φ (sourceSpatialReflection (p := p)).toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt
  rw [href] at hcomp
  have he : C ∘ sourceSpatialReflection = C := funext fun ψ =>
    sourceBoundaryCharacteristic_spatialReflection hp hp1 b ψ z
  change HasFDerivAt (C ∘ sourceSpatialReflection) _ φ at hcomp
  rw [he] at hcomp
  have hd := congrArg (fun L : CoeffPair p →L[ℂ] ℂ => L v) (hcomp.unique hC)
  rw [fderiv_canonicalPeriodOneBoundaryRoot_apply hp hp1 b φ hφ n,
    fderiv_canonicalPeriodOneBoundaryRoot_apply hp hp1 b φ hφ n]
  exact congrArg (fun x : ℂ => -x / deriv (periodOneBoundaryCharacteristic hp hp1 b φ) z) hd

/-- The actual Dirichlet sequence derivative restricted to symmetric complex directions. -/
def symmetricDirichletDerivative (φ : CoeffPair 2) : Coeff 2 →L[ℂ] Coeff 2 :=
  (fderiv ℂ (sourceBoundaryDisplacement (p := 2) (by simp) (by norm_num) .dirichlet) φ).comp
    (complexSymmetricSourceCoefficients 2)

theorem symmetricDirichletDerivative_apply (φ : CoeffPair 2)
    (hφ : IsRealType (CoeffPair.toMax 2 φ)) (a : Coeff 2) (n : ℤ) :
    symmetricDirichletDerivative φ a n =
      (fderiv ℂ (fun ψ : CoeffPair 2 => canonicalPeriodOneBoundaryRoots
        (by simp) (by norm_num) .dirichlet ψ n) φ) (complexSymmetricSourceCoefficients 2 a) := by
  obtain ⟨_,_,hr,hD⟩ := exists_sourceBoundaryDisplacement_analytic_common_domain
    (p := 2) (by simp) (by norm_num)
  exact fderiv_sourceBoundaryDisplacement_apply_of_differentiableAt
    (by simp) (by norm_num) .dirichlet φ _ n (hD .dirichlet φ (hr hφ)).differentiableAt

/-- Each coordinate vector has a preimage under the actual symmetric Dirichlet derivative. -/
theorem single_mem_range_symmetricDirichletDerivative (φ : CoeffPair 2)
    (hφ : IsRealType (CoeffPair.toMax 2 φ)) (href : sourceSpatialReflection φ = φ)
    (m : ℤ) : lp.single 2 m (1 : ℂ) ∈ (symmetricDirichletDerivative φ).range := by
  let v : CoeffPair 2 := (-2 : ℂ) • sourceHamiltonianVector (by norm_num)
    (sourceBoundaryFloquetLogAt (by simp) (by norm_num) .dirichlet m φ) φ
  refine ⟨((1/2 : ℂ) • (v + sourceSpatialReflection v)).snd, ?_⟩
  change symmetricDirichletDerivative φ (((1/2 : ℂ) • (v + sourceSpatialReflection v)).snd) = _
  ext n
  rw [symmetricDirichletDerivative_apply φ hφ, complexSymmetricSourceCoefficients_average]
  simp only [map_smul, map_add, smul_eq_mul]
  rw [fderiv_boundaryRoot_spatialReflection_of_fixed (by simp) (by norm_num) .dirichlet φ hφ href]
  have hv : (fderiv ℂ (fun ψ : CoeffPair 2 => canonicalPeriodOneBoundaryRoots
      (by simp) (by norm_num) .dirichlet ψ n) φ) v = if n = m then 1 else 0 := by
    dsimp only [v]
    rw [map_smul, fderiv_apply_sourceHamiltonianVector,
      sourceBracket_boundaryRoot_floquetLog_eq (by simp) (by norm_num) (by norm_num) .dirichlet φ hφ]
    split_ifs <;> norm_num
  rw [hv]
  by_cases hn : n = m
  · subst n; norm_num
  · simp [hn]

/-- The symmetric Dirichlet derivative differs compactly from identity at every real source. -/
theorem isCompactOperator_symmetricDirichletDerivative_sub_id (φ : CoeffPair 2)
    (hφ : IsRealType (CoeffPair.toMax 2 φ)) :
    IsCompactOperator (symmetricDirichletDerivative φ - 1 : Coeff 2 →L[ℂ] Coeff 2) := by
  have hc := (source_spectral_sequence_derivatives_compact_of_realType φ hφ).2.comp_clm
    (complexSymmetricSourceCoefficients 2)
  have hz : symmetricDirichletDerivative 0 = 1 := by
    ext a n
    rw [symmetricDirichletDerivative_apply 0 (by simp), fderiv_canonicalPeriodOneBoundaryRoot_zero]
    simp only [complexSymmetricSourceCoefficients_fst, complexSymmetricSourceCoefficients_snd,
      neg_neg, BoundaryCondition.extensionSign, one_apply_eq_self]
    ring
  have he : (fderiv ℂ (sourceBoundaryDisplacement (p := 2) (by simp) (by norm_num) .dirichlet) φ -
      fderiv ℂ (sourceBoundaryDisplacement (p := 2) (by simp) (by norm_num) .dirichlet) 0).comp
        (complexSymmetricSourceCoefficients 2) = symmetricDirichletDerivative φ - 1 := by
    rw [← hz]
    rfl
  change IsCompactOperator ((fderiv ℂ (sourceBoundaryDisplacement (p := 2) (by simp) (by norm_num) .dirichlet) φ -
    fderiv ℂ (sourceBoundaryDisplacement (p := 2) (by simp) (by norm_num) .dirichlet) 0).comp
      (complexSymmetricSourceCoefficients 2)) at hc
  rwa [he] at hc

/-- The Dirichlet derivative on the symmetric complex slice is bijective at every
real reflection-fixed Hilbert source, including sources with closed gaps. -/
theorem bijective_symmetricDirichletDerivative (φ : CoeffPair 2)
    (hφ : IsRealType (CoeffPair.toMax 2 φ)) (href : sourceSpatialReflection φ = φ) :
    Function.Bijective (symmetricDirichletDerivative φ) := by
  apply NLS.CompactSpectrum.bijective_of_denseRange_compact_sub_id _
    (isCompactOperator_symmetricDirichletDerivative_sub_id φ hφ)
  have hs (m : ℤ) (z : ℂ) : lp.single 2 m z ∈ (symmetricDirichletDerivative φ).range := by
    have h := (symmetricDirichletDerivative φ).range.smul_mem z
      (single_mem_range_symmetricDirichletDerivative φ hφ href m)
    simpa only [← lp.single_smul, smul_eq_mul, mul_one] using h
  have hf : range (Coeff.ofFinsupp (p := 2)) ⊆ range (symmetricDirichletDerivative φ) := by
    rintro _ ⟨a,rfl⟩
    change Coeff.ofFinsupp a ∈ (symmetricDirichletDerivative φ).range
    rw [Coeff.ofFinsupp_eq_sum_single]
    exact Submodule.sum_mem _ fun m _ => hs m (a m)
  intro a
  exact closure_mono hf (Coeff.denseRange_ofFinsupp (by simp) a)

end NLS.ZakharovShabat
