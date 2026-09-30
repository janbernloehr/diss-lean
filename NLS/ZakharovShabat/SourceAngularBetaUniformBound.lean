import NLS.ZakharovShabat.SourceAngularBetaUniformSelectedBound
import NLS.ZakharovShabat.SourceAngularBetaUniformTailBound

/-!
# One local beta estimate for every off-diagonal pair

The selected-gap tail has fixed radii and an index-uniform factor bound.
Each remaining selected chart has its own bound uniform in the deleted
index. A finite intersection and sum of constants give one complex
source neighborhood and constant for every pair of integer indices.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourcePsiSquaredGapComplexExtension
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The complete quantitative estimate of Theorem 13.1(i) near every
real source, uniformly in both indices throughout one complex neighborhood. -/
theorem exists_local_uniform_sourceAngularBeta_bound
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 W₀ s)
    (W : Set (CoeffPair p)) (hW : IsOpen W) (hWW₀ : W ⊆ W₀)
    (hA : ∀ ψ ∈ W, ∀ k : ℤ,
      AnalyticAt ℂ (fun χ : CoeffPair p => canonicalPeriodicMidpoint hp hp1
        (periodOnePotential χ) (periodOnePotential_mem χ) k) ψ ∧
      AnalyticAt ℂ (fun χ : CoeffPair p => (canonicalPeriodicGap hp hp1
        (periodOnePotential χ) (periodOnePotential_mem χ) k)^2) ψ)
    (φ : CoeffPair p) (hφ : φ ∈ W) (hreal : IsRealType (CoeffPair.toMax p φ)) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧ U ⊆ W ∧
      ∃ C : ℝ, 0 < C ∧ ∀ ψ ∈ U, ∀ n m : ℤ, m ≠ n →
        ‖sourceAngularBeta hp hp1 n m s ψ‖ ≤ C *
          (‖sourcePeriodicGapDisplacement hp hp1 ψ m‖ +
            ‖canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m-
              sourceStandardRootMidpoint hp hp1 ψ m‖) / |((n-m : ℤ) : ℝ)| := by
  classical
  obtain ⟨Ut,hUt,hφt,hUtW,K,Ct,hCt,htail⟩ :=
    hs.exists_local_uniform_sourceAngularBeta_tail_bound W hW hWW₀ hA φ hφ hreal
  have hcharts (m : ℤ) := hs.toSourcePsiIsolatingComplexExtension.exists_local_joint_angular_annulus_primitives
    W hW hWW₀ hA φ hφ hreal m
  choose Vm c T r R z₀ hφm Dm using hcharts
  have hlocal (m : ℤ) := (Dm m).exists_local_uniform_deletedIndices_beta_bound hs hWW₀ φ (hφm m) hreal
  choose Um hUm hφUm _ Cm hCm hbound using hlocal
  let S := Finset.Icc (-(K:ℤ)) (K:ℤ)
  have hevent : ∀ᶠ ψ : CoeffPair p in 𝓝 φ, ∀ m ∈ S, ψ ∈ Um m := by
    rw [Finset.eventually_all]
    intro m _
    exact (hUm m).mem_nhds (hφUm m)
  obtain ⟨H,hHsub,hH,hφH⟩ := _root_.mem_nhds_iff.mp hevent
  let B := ∑ m ∈ S, Cm m
  have hB : 0 ≤ B := Finset.sum_nonneg (fun m _ => (hCm m).le)
  let C := Ct+B
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨Ut ∩ H,hUt.inter hH,⟨hφt,hφH⟩,inter_subset_left.trans hUtW,C,hC,?_⟩
  intro ψ hψ n m hmn
  by_cases hm : K < m.natAbs
  · exact (htail ψ hψ.1 n m hm hmn).trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hB : Ct ≤ C) (by positivity)) (abs_nonneg _))
  · have hmS : m ∈ S := by simp only [S,Finset.mem_Icc]; omega
    have hmB : Cm m ≤ B := Finset.single_le_sum (fun k _ => (hCm k).le) hmS
    have hmC : Cm m ≤ C := by dsimp only [C]; linarith
    exact (hbound m ψ (hHsub hψ.2 m hmS) n hmn).trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hmC (by positivity)) (abs_nonneg _))

end SourcePsiSquaredGapComplexExtension
end NLS.ZakharovShabat
