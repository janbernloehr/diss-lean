import NLS.ZakharovShabat.SourcePsiOriginalSolutionGap

/-!
# Global solutions of the original real psi equation

The unique global real analytic root map solves the original equation.
Its graph lies in every original disk family wherever that family is
admissible. Pointwise uniqueness requires root placement, not prior gap
placement. Solutions converge in the real lp norm with their sources.
-/

noncomputable section
open Set Complex Metric Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- An actual real equation zero lying in an original deleted placement domain. -/
def SourcePsiOriginalRealSolution (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (φ : realTypeSourceSubmodule p) (a : RealDeletedCoeff p n) : Prop :=
  sourcePsiOriginalRealEquation hp hp1 n a φ = 0 ∧
    ∃ V : Set (CoeffPair p), ∃ D : ℤ → Set ℂ, ∃ c : ℝ,
      SourceIsolatingNeighborhoods hp hp1 V D c ∧ (φ,a) ∈ sourcePsiOriginalDeletedOmega V D n

/-- The graph lies in every supplied original disk family over its real sources. -/
theorem SourceIsolatingNeighborhoods.originalRootReal_graph
    {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)} {D : ℤ → Set ℂ} {c : ℝ}
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (φ : realTypeSourceSubmodule p) (hφV : (φ:CoeffPair p) ∈ V) (n : ℤ) :
    (φ,sourcePsiOriginalRootReal hp hp1 n φ) ∈ sourcePsiOriginalDeletedOmega V D n :=
  ⟨hφV,fun m hmn => hD.gap φ hφV m (sourcePsiOriginalRootReal_mem_gap hp hp1 n m hmn φ)⟩

/-- Global solvability with original domain membership. -/
theorem SourceLemma12_4Data.originalRootReal_solution
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceLemma12_4Data hp hp1 W) (hW : IsOpen W) (hR : realTypeSourceLocus p ⊆ W)
    (n : ℤ) (φ : realTypeSourceSubmodule p) :
    SourcePsiOriginalRealSolution hp hp1 n φ (sourcePsiOriginalRootReal hp hp1 n φ) := by
  obtain ⟨V,_,_,hφV,_,D,c,hD⟩ := H.previous.quotients.neighborhoods φ (hR φ.property)
  exact ⟨H.originalRootReal_solves hW hR n φ,V,D,c,hD.toSourceIsolatingNeighborhoods,
    hD.toSourceIsolatingNeighborhoods.originalRootReal_graph φ hφV n⟩

/-- Any original-domain real solution is the canonical solution. -/
theorem SourceLemma12_4Data.originalRealSolution_unique
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceLemma12_4Data hp hp1 W) (φ : realTypeSourceSubmodule p) (hφW : (φ:CoeffPair p) ∈ W)
    (n : ℤ) (a : RealDeletedCoeff p n) (ha : SourcePsiOriginalRealSolution hp hp1 n φ a) :
    a = sourcePsiOriginalRootReal hp hp1 n φ := by
  obtain ⟨hz,V,D,c,hD,hφV,hplace⟩ := ha
  exact H.originalRealEquation_zero_unique hD φ hφW hφV n a hplace hz

/-- The unique global real analytic map solving the original equation. -/
theorem SourceLemma12_4Data.existsUnique_originalRealSolution
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceLemma12_4Data hp hp1 W) (hW : IsOpen W) (hR : realTypeSourceLocus p ⊆ W) (n : ℤ) :
    ∃! s : realTypeSourceSubmodule p → RealDeletedCoeff p n,
      AnalyticOnNhd ℝ s univ ∧ ∀ φ, SourcePsiOriginalRealSolution hp hp1 n φ (s φ) := by
  refine ⟨sourcePsiOriginalRootReal hp hp1 n,
    ⟨analyticOnNhd_sourcePsiOriginalRootReal hp hp1 n,H.originalRootReal_solution hW hR n⟩,?_⟩
  intro s hs
  funext φ
  exact H.originalRealSolution_unique φ (hR φ.property) n (s φ) (hs.2 φ)

/-- Full real lp-norm convergence of solutions along converging source sequences. -/
theorem SourceLemma12_4Data.originalRealSolution_tendsto
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceLemma12_4Data hp hp1 W) (hR : realTypeSourceLocus p ⊆ W) (n : ℤ)
    (φ : realTypeSourceSubmodule p) (ψ : ℕ → realTypeSourceSubmodule p)
    (hψ : Tendsto ψ atTop (𝓝 φ)) (a : ℕ → RealDeletedCoeff p n)
    (ha : ∀ k, SourcePsiOriginalRealSolution hp hp1 n (ψ k) (a k)) :
    Tendsto a atTop (𝓝 (sourcePsiOriginalRootReal hp hp1 n φ)) := by
  have he : a = fun k => sourcePsiOriginalRootReal hp hp1 n (ψ k) :=
    funext (fun k => H.originalRealSolution_unique (ψ k) (hR (ψ k).property) n (a k) (ha k))
  rw [he]
  exact (analyticOnNhd_sourcePsiOriginalRootReal hp hp1 n φ (mem_univ _)).continuousAt.tendsto.comp hψ

end NLS.ZakharovShabat
