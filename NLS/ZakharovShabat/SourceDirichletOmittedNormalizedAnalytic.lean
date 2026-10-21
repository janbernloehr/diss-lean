import NLS.ZakharovShabat.SourceDirichletOmittedSquareAnalytic
import NLS.SequenceSpaces.NormalizedRootBranchPropagation
import NLS.ZakharovShabat.SourcePsiComplexRootDomain

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual omitted product normalized by its free parity sign. -/
def sourceDirichletOmittedNormalized (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) : ℂ :=
  (-1 : ℂ)^n.natAbs * sourceStandardRootOmittedProduct hp hp1 n ψ
    (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n)

namespace SourceLemma12_12Data
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The retained original angular domain is preconnected, as supplied by its root atlas. -/
theorem original_domain_preconnected (H : SourceLemma12_12Data hp hp1 W₀ W s) :
    IsPreconnected W := by
  obtain ⟨A,hW,_⟩ := H.previous.previous.atlas
  rw [← hW]
  exact A.toSourcePsiComplexRootAtlas.isSimplyConnected_domain.isPathConnected.isConnected.isPreconnected

/-- The full normalized omitted-product error is Banach analytic on unchanged W. -/
theorem dirichlet_omitted_normalized_analytic (H : SourceLemma12_12Data hp hp1 W₀ W s) :
    AnalyticOnNhd ℂ (fun ψ => Coeff.ofFunctionOrZero p
      (fun n => sourceDirichletOmittedNormalized hp hp1 ψ n-1)) W ∧
      ∀ ψ ∈ W, ∀ n, Coeff.ofFunctionOrZero p
        (fun m => sourceDirichletOmittedNormalized hp hp1 ψ m-1) n =
          sourceDirichletOmittedNormalized hp hp1 ψ n-1 := by
  have hsign (n : ℤ) : ((-1 : ℂ)^n.natAbs)^2 = 1 := by
    rw [← pow_mul,mul_comm n.natAbs 2,pow_mul]
    norm_num
  obtain ⟨hec,he⟩ := H.dirichlet_omitted_square_analytic
  apply Coeff.analytic_normalized_root_error hp hp1
    H.original_theta_common_domain.source_open H.original_domain_preconnected
    (sourceDirichletOmittedNormalized hp hp1)
    (fun n ψ hψ => analyticAt_const.mul (H.dirichlet_omitted_sample_data ψ hψ n).2)
    (sourceDirichletOmittedSquareRemainder hp hp1) hec.continuousOn
    (fun ψ hψ n => by
      rw [he ψ hψ n]
      simp only [sourceDirichletOmittedSquareError,sourceDirichletOmittedNormalized,mul_pow,hsign,one_mul])
    0 (H.original_theta_common_domain.real_subset (by simp [realTypeSourceLocus]))
  apply (memlp_sourceStandardRootOmittedProduct_boundary_sub_sign hp hp1 .dirichlet 0 (by simp)).mono'
  intro n
  have hid : sourceDirichletOmittedNormalized hp hp1 (0 : CoeffPair p) n-1 =
      (-1 : ℂ)^n.natAbs * (sourceStandardRootOmittedProduct hp hp1 n 0
        (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet 0 n)-(-1 : ℂ)^n.natAbs) := by
    simp only [sourceDirichletOmittedNormalized,mul_sub,← sq,hsign]
  rw [hid,norm_mul]
  simp

end SourceLemma12_12Data
end NLS.ZakharovShabat
