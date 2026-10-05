import NLS.ZakharovShabat.SourceFrequencyOrigin
import NLS.SequenceSpaces.RealCoeffExponent
import Mathlib.Analysis.Convex.Topology

/-! # The connected action domain containing the real sources -/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderTriple p q]
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B X : Set (CoeffPair p)}
  {t : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- All real-source actions belong to the component of zero of any open
set containing them. This uses the actual action map on the whole real space. -/
theorem SourceBirkhoffMapComplexData.real_actions_mem_zero_component
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) {V : Set (Coeff q)}
    (hcenter : ∀ ψ : realTypeSourceSubmodule p, sourceActionSequence (q := q) hp hp1 t ψ.val ∈ V)
    (ψ : realTypeSourceSubmodule p) :
    sourceActionSequence (q := q) hp hp1 t ψ.val ∈ connectedComponentIn V 0 := by
  let I := fun φ : realTypeSourceSubmodule p => sourceActionSequence (q := q) hp hp1 t φ.val
  have hI : Continuous I := by
    apply continuous_iff_continuousAt.mpr
    intro φ
    exact (D.actionSequence_analytic φ.val (D.real_subset φ.property)).continuousAt.comp
      continuous_subtype_val.continuousAt
  have hconn : IsPreconnected (range I) := isPreconnected_range hI
  have hz : (0 : Coeff q) ∈ range I := ⟨0,D.actionSequence_zero⟩
  exact hconn.subset_connectedComponentIn hz (by rintro _ ⟨φ,rfl⟩; exact hcenter φ) ⟨ψ,rfl⟩

omit [Fact (1 ≤ p)] [p.HolderTriple p q] in
/-- The nonnegative summable action cone also lies in the component of zero. -/
theorem nonnegative_summable_actions_mem_zero_component {V : Set (Coeff q)}
    (hpos : ∀ b : RealCoeff 1, (∀ n, 0 ≤ b n) →
      Coeff.exponentInclusion (Fact.out : 1 ≤ q) (RealCoeff.complexCLM 1 b) ∈ V)
    (b : RealCoeff 1) (hb : ∀ n, 0 ≤ b n) :
    Coeff.exponentInclusion (Fact.out : 1 ≤ q) (RealCoeff.complexCLM 1 b) ∈
      connectedComponentIn V 0 := by
  let γ := fun a : ℝ => Coeff.exponentInclusion (Fact.out : 1 ≤ q) (RealCoeff.complexCLM 1 (a • b))
  have hγ : Continuous γ := by dsimp [γ]; fun_prop
  have hconn : IsPreconnected (γ '' Icc 0 1) := isPreconnected_Icc.image γ hγ.continuousOn
  have hz : (0 : Coeff q) ∈ γ '' Icc 0 1 := ⟨0,by simp,by simp [γ]⟩
  have hV : γ '' Icc 0 1 ⊆ V := by
    rintro _ ⟨a,ha,rfl⟩
    apply hpos (a • b)
    intro n
    change 0 ≤ a * b n
    exact mul_nonneg ha.1 (hb n)
  exact hconn.subset_connectedComponentIn hz hV ⟨1,by simp,by simp [γ]⟩

end NLS.ZakharovShabat
