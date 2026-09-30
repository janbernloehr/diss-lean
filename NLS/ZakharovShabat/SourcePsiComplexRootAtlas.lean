import NLS.ZakharovShabat.SourcePsiComplexBranchCompatibility
import NLS.ComplexAnalysis.GlueHolomorphicCharts

/-!
# One complex source domain for all canonical psi root maps

Choose a uniform branch family at each real potential. Their compatible
source balls form one open domain, independent of the deleted index.
Gluing preserves the local branches, canonical real roots, and actual
retained contour equations. Projection to the real locus stays inside
each ball and the whole segment to that projection stays in the union.
-/

noncomputable section
open Set Filter Topology Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

structure SourcePsiComplexRootAtlas (hp : p ≠ ⊤) (hp1 : 1 < p) where
  tube : (φ : realTypeSourceLocus p) → SourcePsiUniformEquationTube hp hp1 φ
  localBranch : (φ : realTypeSourceLocus p) → SourcePsiUniformComplexBranchFamily (tube φ)

theorem nonempty_sourcePsiComplexRootAtlas (hp : p ≠ ⊤) (hp1 : 1 < p) :
    Nonempty (SourcePsiComplexRootAtlas hp hp1) := by
  classical
  let D := fun φ => Classical.choice (nonempty_sourcePsiUniformEquationTube hp hp1 φ)
  exact ⟨⟨D,fun φ => Classical.choice (nonempty_sourcePsiUniformComplexBranchFamily (D φ))⟩⟩

namespace SourcePsiComplexRootAtlas
variable {hp : p ≠ ⊤} {hp1 : 1 < p} (A : SourcePsiComplexRootAtlas hp hp1)

def sourceBall (φ : realTypeSourceLocus p) : Set (CoeffPair p) :=
  ball φ.val (A.localBranch φ).sourceRadius

def domain : Set (CoeffPair p) := ⋃ φ, A.sourceBall φ

def branch (n : ℤ) : CoeffPair p → DeletedCoeff p n :=
  NLS.ComplexAnalysis.glueHolomorphicCharts A.sourceBall (fun φ => (A.localBranch φ).branch n)

theorem isOpen_domain : IsOpen A.domain :=
  isOpen_iUnion (fun _ => isOpen_ball)

theorem realType_subset_domain : realTypeSourceLocus p ⊆ A.domain := by
  intro φ hφ
  exact mem_iUnion.mpr ⟨⟨φ,hφ⟩,mem_ball_self (A.localBranch ⟨φ,hφ⟩).sourceRadius_pos⟩

theorem eq_local (n : ℤ) (φ : realTypeSourceLocus p) :
    EqOn (A.branch n) ((A.localBranch φ).branch n) (A.sourceBall φ) :=
  NLS.ComplexAnalysis.glueHolomorphicCharts_eq_on A.sourceBall
    (fun χ => (A.localBranch χ).branch n)
    (fun χ θ => (A.localBranch χ).eqOn_sourceBall_overlap (A.localBranch θ) n) φ

theorem analytic (n : ℤ) : AnalyticOnNhd ℂ (A.branch n) A.domain := by
  intro ψ hψ
  obtain ⟨φ,hφ⟩ := mem_iUnion.mp hψ
  have hnear := NLS.ComplexAnalysis.glueHolomorphicCharts_eventuallyEq A.sourceBall
    (fun χ => (A.localBranch χ).branch n) (fun _ => isOpen_ball)
    (fun χ θ => (A.localBranch χ).eqOn_sourceBall_overlap (A.localBranch θ) n) φ ψ hφ
  exact ((A.localBranch φ).analytic n ψ hφ).congr hnear.symm

theorem eq_sourcePsiGapRoot_of_real (n : ℤ) (φ : realTypeSourceLocus p) :
    A.branch n φ.val = sourcePsiGapRoot hp hp1 n φ := by
  have hφ : φ.val ∈ A.sourceBall φ := mem_ball_self (A.localBranch φ).sourceRadius_pos
  exact (A.eq_local n φ hφ).trans ((A.localBranch φ).eq_sourcePsiGapRoot_of_real n φ hφ)

theorem contour_equations (n : ℤ) (ψ : CoeffPair p) (hψ : ψ ∈ A.domain) :
    ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
      sourcePsiRealCenteredContourFamily hp hp1 ψ c R ∧
      ∀ m, sourcePsiEquationCoordinate hp hp1 n m (A.branch n ψ : Coeff p) ψ (c m) (R m) = 0 := by
  obtain ⟨φ,hφ⟩ := mem_iUnion.mp hψ
  rw [A.eq_local n φ hφ]
  exact (A.localBranch φ).contour_equations n ψ hφ

theorem contour_zero (n : ℤ) (ψ : CoeffPair p) (hψ : ψ ∈ A.domain) :
    ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
      sourcePsiRealCenteredContourFamily hp hp1 ψ c R ∧
      ∀ m : ℤ, m ≠ n →
        sourcePsiContour hp hp1 n (A.branch n ψ : Coeff p) ψ (c m) (R m) = 0 := by
  obtain ⟨c,R,hfamily,hcoord⟩ := A.contour_equations n ψ hψ
  refine ⟨c,R,hfamily,?_⟩
  intro m hmn
  have hnm : ((n-m : ℤ) : ℂ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr hmn.symm
  have hπ : (2*Real.pi : ℂ) ≠ 0 :=
    mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
  have hzero := hcoord m
  rw [sourcePsiEquationCoordinate] at hzero
  exact (mul_eq_zero.mp hzero).resolve_left (mul_ne_zero hnm hπ)

theorem sourceRealPart_mem_sourceBall (φ : realTypeSourceLocus p)
    (ψ : CoeffPair p) (hψ : ψ ∈ A.sourceBall φ) : sourceRealPart ψ ∈ A.sourceBall φ :=
  (dist_sourceRealPart_le_of_realType hp φ.val φ.property ψ).trans_lt hψ

theorem sourceRealPart_mem_domain (ψ : CoeffPair p) (hψ : ψ ∈ A.domain) :
    sourceRealPart ψ ∈ A.domain := by
  obtain ⟨φ,hφ⟩ := mem_iUnion.mp hψ
  exact mem_iUnion.mpr ⟨φ,A.sourceRealPart_mem_sourceBall φ ψ hφ⟩

theorem segment_sourceRealPart_subset_domain (ψ : CoeffPair p) (hψ : ψ ∈ A.domain) :
    segment ℝ ψ (sourceRealPart ψ) ⊆ A.domain := by
  obtain ⟨φ,hφ⟩ := mem_iUnion.mp hψ
  exact ((convex_ball φ.val (A.localBranch φ).sourceRadius).segment_subset
    hφ (A.sourceRealPart_mem_sourceBall φ ψ hφ)).trans
    (subset_iUnion A.sourceBall φ)

end SourcePsiComplexRootAtlas
end NLS.ZakharovShabat
