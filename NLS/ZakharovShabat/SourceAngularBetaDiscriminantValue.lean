import NLS.ZakharovShabat.SourceAngularBetaDiscriminantKernel
import NLS.ZakharovShabat.SourcePsiDirichletDiscriminantInterpolation

/-! # The exact actual beta-correction/discriminant bracket

The proved full beta derivative series and filled actual interpolation
have the same off-diagonal kernel sums. Subtracting the omitted diagonal
identifies the full beta-correction bracket at every spectral parameter.
-/

noncomputable section
set_option maxHeartbeats 800000
open Set Metric Complex Filter Topology NLS.Poisson
open scoped ENNReal Classical
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceAngularThetaCommonDomainData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (j : ℤ) → CoeffPair p → DeletedCoeff p j}

/-- The actual full beta-correction/discriminant bracket is minus
half the numerator minus its omitted diagonal kernel contribution.
No selected gap is required to be open. -/
theorem sourceBracket_betaCorrection_discriminant_eq
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (h2p : (2 : ℝ≥0∞) ≤ p) (n : ℤ) (φ : realTypeSourceLocus p) (w : ℂ) :
    sourceBracket h2p (sourceAngularBetaCorrection hp hp1 n s)
      (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ) w) φ.val =
      -sourcePsiCandidate n (w,(s n φ.val : Coeff p))/2-
        sourcePsiCandidate n (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val n,(s n φ.val : Coeff p))*
          sourceDirichletDiscriminantKernel hp hp1 n φ.val w := by
  let F : ℤ → ℂ := fun m =>
    sourcePsiCandidate n (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val m,(s n φ.val : Coeff p))*
      sourceDirichletDiscriminantKernel hp hp1 m φ.val w
  have hi := (tendsto_sourcePsiDirichlet_discriminantKernelSums hp hp1 n (s n φ.val : Coeff p) φ w).sub
    (tendsto_const_nhds (x := F n))
  have hoff : Tendsto (fun N : ℕ => ∑ m ∈ Finset.Icc (-(N : ℤ)) N,
      sourceAngularBetaDiscriminantKernelTerm hp hp1 n s φ.val w m) atTop
      (𝓝 (-sourcePsiCandidate n (w,(s n φ.val : Coeff p))/2-F n)) := by
    apply hi.congr'
    filter_upwards [eventually_ge_atTop n.natAbs] with N hN
    have hmem : n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := by simp only [Finset.mem_Icc]; omega
    symm
    calc
      _ = ∑ m ∈ Finset.Icc (-(N : ℤ)) N, (F m-(if m = n then F n else 0)) := by
        apply Finset.sum_congr rfl
        intro m _
        change (if m = n then 0 else F m) = F m-(if m = n then F n else 0)
        by_cases hm : m = n <;> simp [hm]
      _ = (∑ m ∈ Finset.Icc (-(N : ℤ)) N, F m)-F n := by
        rw [Finset.sum_sub_distrib]
        simp only [Finset.sum_ite_eq',hmem,ite_true]
  exact tendsto_nhds_unique (D.tendsto_betaDiscriminantKernels h2p n φ w) hoff

/-- The omitted diagonal makes the full beta correction commute with
the discriminant evaluated at its own base-source Dirichlet root. -/
theorem sourceBracket_betaCorrection_discriminant_at_root_eq_zero
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (h2p : (2 : ℝ≥0∞) ≤ p) (n : ℤ) (φ : realTypeSourceLocus p) :
    sourceBracket h2p (sourceAngularBetaCorrection hp hp1 n s)
      (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ)
        (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val n)) φ.val = 0 := by
  rw [D.sourceBracket_betaCorrection_discriminant_eq h2p n φ,
    sourceDirichletDiscriminantKernel_at_root hp hp1 n φ.val φ.property]
  ring

end SourceAngularThetaCommonDomainData
end NLS.ZakharovShabat
