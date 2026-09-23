import NLS.ZakharovShabat.SourceIsolatingSpectrum
import Mathlib.Analysis.Normed.Module.RCLike.Real

/-!
# Circular boundaries of the source isolating discs

Every assigned disc is a positive-radius ball. Its boundary misses the
entire periodic spectrum: the indexed endpoints lie strictly inside,
while endpoints at other indices lie in disjoint open discs.
-/

noncomputable section
open Set Metric Complex
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Center of the fixed central or free high-index assigned disc. -/
def sourceIsolatingCenter (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (N : ℕ) (n : ℤ) : ℂ :=
  if n.natAbs ≤ N then
    (((canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re +
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re)/2 : ℝ)
  else (Real.pi : ℂ)*n

/-- Radius of the fixed central or free high-index assigned disc. -/
def sourceIsolatingRadius (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (N : ℕ) (ε : ℝ) (n : ℤ) : ℝ :=
  if n.natAbs ≤ N then
    ((canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re -
      (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re)/2 + ε
  else Real.pi/4

/-- Every assigned isolating disc is the ball with its explicit center
and radius. -/
theorem sourceIsolatingDisc_eq_ball (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (N : ℕ) (ε : ℝ) (n : ℤ) :
    sourceIsolatingDisc hp hp1 φ N ε n =
      ball (sourceIsolatingCenter hp hp1 φ N n)
        (sourceIsolatingRadius hp hp1 φ N ε n) := by
  by_cases hn : n.natAbs ≤ N
  · simp only [sourceIsolatingDisc, sourceIsolatingCenter, sourceIsolatingRadius,
      if_pos hn, sourceClusterDisc]
  · simp only [sourceIsolatingDisc, sourceIsolatingCenter, sourceIsolatingRadius,
      if_neg hn, refinedResonantDisk]

/-- At a real-type base potential, a positive central enlargement makes
every assigned disc radius positive. -/
theorem sourceIsolatingRadius_pos (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p)
    (N : ℕ) (ε : ℝ) (hε : 0 < ε) (n : ℤ) :
    0 < sourceIsolatingRadius hp hp1 φ N ε n := by
  by_cases hn : n.natAbs ≤ N
  · simp only [sourceIsolatingRadius, if_pos hn]
    have hle := re_le_of_complexLexLE
      ((canonicalPeriodicEndpoints_spec hp hp1 (periodOnePotential φ)
        (periodOnePotential_mem φ)).2.1 n)
    linarith
  · simp only [sourceIsolatingRadius, if_neg hn]
    positivity

/-- The assigned source discs are open. -/
theorem isOpen_sourceIsolatingDisc (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (N : ℕ) (ε : ℝ) (n : ℤ) :
    IsOpen (sourceIsolatingDisc hp hp1 φ N ε n) := by
  rw [sourceIsolatingDisc_eq_ball]
  exact isOpen_ball

/-- The boundary of an assigned disc contains no periodic eigenvalue
when all canonical endpoints lie in their pairwise disjoint discs. -/
theorem sourceIsolatingSphere_subset_resolventSet
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : CoeffPair p)
    (N : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hcluster : ∀ m : ℤ, sourceSpectralCluster hp hp1 ψ m ⊆
      sourceIsolatingDisc hp hp1 φ N ε m)
    (hdisjoint : ∀ i j : ℤ, i ≠ j →
      Disjoint (sourceIsolatingDisc hp hp1 φ N ε i)
        (sourceIsolatingDisc hp hp1 φ N ε j))
    (n : ℤ) :
    sphere (sourceIsolatingCenter hp hp1 φ N n)
      (sourceIsolatingRadius hp hp1 φ N ε n) ⊆
        resolventSet hp (periodOnePotential ψ) := by
  intro z hz
  have hnot : z ∉ periodicSpectrum hp (periodOnePotential ψ) := by
    intro hspec
    obtain ⟨m, hm⟩ := (canonicalPeriodicEndpoints_exhaustive hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) z).mp hspec
    have hzm : z ∈ sourceIsolatingDisc hp hp1 φ N ε m := by
      rcases hm with hL | hR
      · exact hL ▸ hcluster m (Or.inl rfl)
      · exact hR ▸ hcluster m (Or.inr (Or.inl rfl))
    by_cases hmn : n = m
    · subst m
      rw [sourceIsolatingDisc_eq_ball] at hzm
      have heq := mem_sphere.mp hz
      have hlt := mem_ball.mp hzm
      linarith
    · have hzclosure : z ∈ closure (sourceIsolatingDisc hp hp1 φ N ε n) := by
        rw [sourceIsolatingDisc_eq_ball,
          closure_ball _ (sourceIsolatingRadius_pos hp hp1 φ N ε hε n).ne']
        exact sphere_subset_closedBall hz
      exact Set.disjoint_left.mp
        ((hdisjoint n m hmn).closure_left
          (isOpen_sourceIsolatingDisc hp hp1 φ N ε m)) hzclosure hzm
  simpa only [periodicSpectrum, Set.mem_compl_iff, not_not] using hnot

/-- The finite set enclosed by an assigned contour consists exactly of
the two canonical periodic endpoints at its signed index. -/
theorem enclosedPeriodicSpectrum_sourceIsolating_eq_pair
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : CoeffPair p) (N : ℕ) (ε : ℝ)
    (hcluster : ∀ m : ℤ, sourceSpectralCluster hp hp1 ψ m ⊆
      sourceIsolatingDisc hp hp1 φ N ε m)
    (hdisjoint : ∀ i j : ℤ, i ≠ j →
      Disjoint (sourceIsolatingDisc hp hp1 φ N ε i)
        (sourceIsolatingDisc hp hp1 φ N ε j))
    (n : ℤ) :
    enclosedPeriodicSpectrum hp (periodOnePotential ψ)
      (sourceIsolatingCenter hp hp1 φ N n)
      (sourceIsolatingRadius hp hp1 φ N ε n) =
        {canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n,
         canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n} := by
  ext z
  rw [mem_enclosedPeriodicSpectrum, ← sourceIsolatingDisc_eq_ball]
  have hset := congrArg (fun s : Set ℂ => z ∈ s)
    (source_periodicSpectrum_inter_isolatingDisc_eq_pair hp hp1 φ ψ N ε
      hcluster hdisjoint n)
  simpa only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
    Finset.mem_insert, Finset.mem_singleton] using Iff.of_eq hset

end NLS.ZakharovShabat
