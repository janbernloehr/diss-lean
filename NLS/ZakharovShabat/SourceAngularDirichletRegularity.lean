import NLS.ZakharovShabat.SourceAngularRootSheet
import NLS.ZakharovShabat.SourcePsiLemma12_10
import NLS.ZakharovShabat.FiniteDiscriminant
import Mathlib.Tactic.Ring

/-!
# Dirichlet terminal regularity in assigned spectral discs

Inside the actual pairwise disjoint cluster discs, the anti-discriminant
at `μₘ` vanishes precisely when `μₘ` is one of its own periodic endpoints.
This identifies the regular-terminal hypothesis used for the sheet
construction with the hypothesis stated at the start of Section 13.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Assigned cluster isolation rules out an endpoint from another index.
The equivalence holds for complex potentials as well as real ones. -/
theorem sourceDirichletAntiDiscriminant_eq_zero_iff_endpoints
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ ψ : CoeffPair p) (N : ℕ) (ε : ℝ)
    (hclusters : ∀ k : ℤ, sourceSpectralCluster hp hp1 ψ k ⊆
      sourceIsolatingDisc hp hp1 φ N ε k)
    (hdisjoint : ∀ i j : ℤ, i ≠ j → Disjoint
      (sourceIsolatingDisc hp hp1 φ N ε i) (sourceIsolatingDisc hp hp1 φ N ε j))
    (m : ℤ) :
    let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m
    sourceAntiDiscriminantCandidate hp hp1 ψ μ = 0 ↔
      μ = canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m ∨
      μ = canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m := by
  let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m
  have hid : (canonicalDiscriminant hp (periodOnePotential ψ) μ) ^ 2 - 4 =
      (sourceAntiDiscriminantCandidate hp hp1 ψ μ) ^ 2 :=
    sourceDiscriminant_sq_sub_four_at_canonicalDirichletRoot hp hp1 ψ m
  constructor
  · intro hzero
    have hΔ : (canonicalDiscriminant hp (periodOnePotential ψ) μ) ^ 2 = 4 := by
      apply sub_eq_zero.mp
      rw [hid,hzero]
      simp
    have hspec : μ ∈ periodicSpectrum hp (periodOnePotential ψ) :=
      (canonicalDiscriminant_sq_eq_four_iff_finite hp hp1 _ (periodOnePotential_mem ψ) μ).mp hΔ
    obtain ⟨k,hend⟩ := (canonicalPeriodicEndpoints_exhaustive hp hp1 _
      (periodOnePotential_mem ψ) μ).mp hspec
    have hm : μ ∈ sourceIsolatingDisc hp hp1 φ N ε m :=
      hclusters m (Or.inr (Or.inr (Or.inl rfl)))
    have hk : μ ∈ sourceIsolatingDisc hp hp1 φ N ε k := by
      apply hclusters k
      rcases hend with h | h
      · exact Or.inl h.symm
      · exact Or.inr (Or.inl h.symm)
    have hkm : k = m := by
      by_contra hkm
      exact Set.disjoint_left.mp (hdisjoint k m hkm) hk hm
    subst k
    exact hend.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)
  · intro hend
    have hspec : μ ∈ periodicSpectrum hp (periodOnePotential ψ) := by
      apply (canonicalPeriodicEndpoints_exhaustive hp hp1 _ (periodOnePotential_mem ψ) μ).mpr
      exact ⟨m,hend.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)⟩
    have hΔ := (canonicalDiscriminant_sq_eq_four_iff_finite hp hp1 _
      (periodOnePotential_mem ψ) μ).mpr hspec
    have hδsq : sourceAntiDiscriminantCandidate hp hp1 ψ μ ^ 2 = 0 := by
      rw [← hid,hΔ]
      ring
    exact (sq_eq_zero_iff).mp hδsq

/-- The regular Dirichlet terminal of Section 13 has a unique sign
selected by its nonzero anti-discriminant. -/
theorem sourceDirichletAntiDiscriminant_ne_zero_of_ne_endpoints
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ ψ : CoeffPair p) (N : ℕ) (ε : ℝ)
    (hclusters : ∀ k : ℤ, sourceSpectralCluster hp hp1 ψ k ⊆
      sourceIsolatingDisc hp hp1 φ N ε k)
    (hdisjoint : ∀ i j : ℤ, i ≠ j → Disjoint
      (sourceIsolatingDisc hp hp1 φ N ε i) (sourceIsolatingDisc hp hp1 φ N ε j))
    (m : ℤ)
    (hleft : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m ≠
      canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)
    (hright : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m ≠
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m) :
    sourceAntiDiscriminantCandidate hp hp1 ψ
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m) ≠ 0 := by
  intro hzero
  exact ((sourceDirichletAntiDiscriminant_eq_zero_iff_endpoints hp hp1 φ ψ N ε
    hclusters hdisjoint m).mp hzero).elim hleft hright

namespace SourcePsiIsolatingComplexExtension
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The proved actual psi domain supplies all isolation hypotheses;
only the paper's exclusion of the two terminal endpoints remains. -/
theorem exists_local_angular_dirichlet_sheet
    (hs : SourcePsiIsolatingComplexExtension hp hp1 W s) (hW : IsOpen W)
    (φ : realTypeSourceLocus p) (m : ℤ)
    (hleft : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val m ≠
      canonicalPeriodicLeft hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) m)
    (hright : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val m ≠
      canonicalPeriodicRight hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) m) :
    let w := sourceAntiDiscriminantCandidate hp hp1 φ.val
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val m)
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ.val ∈ V ∧ V ⊆ W ∧
      ∀ ψ ∈ V, let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m
        (μ,ψ) ∈ sourceAngularRootSheetDomain hp w ∧
          sourceAngularRootSheet hp w (μ,ψ) = sourceAntiDiscriminantCandidate hp hp1 ψ μ := by
  obtain ⟨r,hr,N,ε,_,_,hWball,hclusters,hdisjoint,_⟩ := hs.isolation φ
  have hφball : φ.val ∈ ball φ.val r := mem_ball_self hr
  have hw := sourceDirichletAntiDiscriminant_ne_zero_of_ne_endpoints hp hp1 φ.val φ.val N ε
    (hclusters φ.val hφball) hdisjoint m hleft hright
  exact exists_local_sourceAngularRootSheet_dirichlet_normalization hp hp1 W hW φ.val
    φ.property (hWball hφball) m hw

end SourcePsiIsolatingComplexExtension
end NLS.ZakharovShabat
