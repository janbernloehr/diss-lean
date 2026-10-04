import NLS.SequenceSpaces.QuadraticActionLifting
import NLS.ZakharovShabat.SourceBirkhoffInverseChart
import NLS.ZakharovShabat.SourcePositiveActionRealization

/-! # Open complex neighborhoods of the original action values

Real-compatible inverse charts and openness of quadratic actions give
open half-exponent neighborhoods of every real spectral action sequence.
Every point in these neighborhoods is realized by a source in any
prescribed open neighborhood of the real source locus.
-/
noncomputable section
open Set Metric Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderTriple p q]
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W U : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
  {D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s}
  {φ : realTypeSourceSubmodule p}
namespace SourceBirkhoffInverseChart

/-- The open action image of one complex Birkhoff chart. -/
def actionTarget (C : SourceBirkhoffInverseChart D φ U) : Set (Coeff q) :=
  quadraticActionsExponent '' C.target

theorem actionTarget_open (C : SourceBirkhoffInverseChart D φ U) :
    IsOpen (C.actionTarget (q := q)) :=
  isOpenMap_quadraticActionsExponent hp _ C.target_open

theorem action_center_mem (C : SourceBirkhoffInverseChart D φ U) :
    sourceActionSequence (q := q) hp hp1 s φ.val ∈ C.actionTarget :=
  ⟨sourceBirkhoffMap hp hp1 s φ.val,C.center_mem,rfl⟩

/-- Every point of the action target is the original spectral action
sequence of an actual source inside the prescribed neighborhood. -/
theorem exists_source_of_mem_actionTarget (C : SourceBirkhoffInverseChart D φ U)
    (a : Coeff q) (ha : a ∈ C.actionTarget) :
    ∃ ψ ∈ W ∩ U, sourceActionSequence hp hp1 s ψ = a ∧
      ∀ n, sourceComplexAction hp hp1 n ψ = a n := by
  obtain ⟨z,hz,rfl⟩ := ha
  refine ⟨C.inverse z,C.image_subset hz,C.actionSequence_eq z hz,?_⟩
  intro n
  rw [C.action_eq z hz n,quadraticActionsExponent_apply]

end SourceBirkhoffInverseChart

/-- Any open neighborhood of the real source locus realizes an open
complex neighborhood of all real action values, in the Banach half exponent. -/
theorem exists_sourceAction_openNeighborhood (hp : p ≠ ⊤) (hp1 : 1 < p)
    (U : Set (CoeffPair p)) (hU : IsOpen U) (hreal : realTypeSourceLocus p ⊆ U) :
    ∃ V : Set (Coeff q), IsOpen V ∧
      (∀ φ : realTypeSourceSubmodule p, ∃ a ∈ V,
        ∀ n, a n = sourceComplexAction hp hp1 n φ.val) ∧
      ∀ a ∈ V, ∃ ψ ∈ U, ∀ n, sourceComplexAction hp hp1 n ψ = a n := by
  classical
  obtain ⟨W₀,B,W,s,D⟩ := exists_sourceBirkhoffMap_complex_analytic hp hp1
  let C (φ : realTypeSourceSubmodule p) : SourceBirkhoffInverseChart D φ U :=
    (D.exists_inverseChart φ U hU (hreal φ.property)).some
  refine ⟨⋃ φ, (C φ).actionTarget,isOpen_iUnion (fun φ => (C φ).actionTarget_open),?_,?_⟩
  · intro φ
    refine ⟨sourceActionSequence hp hp1 s φ.val,
      mem_iUnion.mpr ⟨φ,(C φ).action_center_mem⟩,?_⟩
    exact D.actionSequence_apply φ.val (D.real_subset φ.property)
  · intro a ha
    obtain ⟨φ,hφ⟩ := mem_iUnion.mp ha
    obtain ⟨ψ,hψ,_,he⟩ := (C φ).exists_source_of_mem_actionTarget a hφ
    exact ⟨ψ,hψ.2,he⟩

/-- The complex action neighborhood contains the entire nonnegative l1
cone in the half-exponent space. Its points are realized inside the given
source neighborhood. This is the geometric input to Theorem 18.1, not yet
analytic descent of the frequency. -/
theorem exists_sourceAction_neighborhood_positiveCone (hp : p ≠ ⊤) (hp1 : 1 < p)
    (h2p : 2 ≤ p) (U : Set (CoeffPair p))
    (hU : IsOpen U) (hreal : realTypeSourceLocus p ⊆ U) :
    ∃ V : Set (Coeff q), IsOpen V ∧
      (∀ b : RealCoeff 1, (∀ n, 0 ≤ b n) →
        Coeff.exponentInclusion (Fact.out : 1 ≤ q) (RealCoeff.complexCLM 1 b) ∈ V) ∧
      ∀ a ∈ V, ∃ ψ ∈ U, ∀ n, sourceComplexAction hp hp1 n ψ = a n := by
  obtain ⟨V,hV,hcenters,hlift⟩ := exists_sourceAction_openNeighborhood (q := q) hp hp1 U hU hreal
  refine ⟨V,hV,?_,hlift⟩
  intro b hb
  obtain ⟨φ,hφ⟩ := exists_source_of_nonnegative_actions hp hp1 h2p b hb
  obtain ⟨a,ha,he⟩ := hcenters φ
  have heq : a = Coeff.exponentInclusion (Fact.out : 1 ≤ q) (RealCoeff.complexCLM 1 b) := by
    ext n
    exact (he n).trans (hφ n)
  rwa [← heq]

end NLS.ZakharovShabat
