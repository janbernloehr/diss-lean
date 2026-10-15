import NLS.ZakharovShabat.SourceSection17Original
import NLS.ZakharovShabat.SourceActionNeighborhood
import NLS.ZakharovShabat.SourceFrequencyConnectedDomain

/-!
# Action domains for the original family

Any open action neighborhood of all real sources can be restricted to an
open connected neighborhood realized inside the original complex domain.
No equality with the entire original complex action image is assumed.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderTriple p q]
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W V : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Spectral action sequences do not depend on the chosen normalized root family
on the intersection of the two complex map domains. -/
theorem SourceSection17OriginalData.actionSequence_eq
    (D : SourceSection17OriginalData hp hp1 W₀ W V s)
    {X₀ B X : Set (CoeffPair p)} {t : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    (E : SourceBirkhoffMapComplexData hp hp1 X₀ B X t)
    (φ : CoeffPair p) (hφ : φ ∈ V) (hφ' : φ ∈ X) :
    sourceActionSequence (q := q) hp hp1 s φ = sourceActionSequence hp hp1 t φ := by
  ext n
  exact (D.complex.actionSequence_apply φ hφ n).trans (E.actionSequence_apply φ hφ' n).symm

/-- Restrict an action neighborhood to a connected image of an open subset
of the original source domain, retaining every real source and positive l1 action. -/
theorem SourceSection17OriginalData.exists_connected_action_image
    (D : SourceSection17OriginalData hp hp1 W₀ W V s) (h2p : 2 ≤ p)
    (T : Set (Coeff q)) (hT : IsOpen T)
    (hrealT : ∀ φ : realTypeSourceSubmodule p, sourceActionSequence hp hp1 s φ.val ∈ T) :
    ∃ U : Set (Coeff q), IsOpen U ∧ IsPreconnected U ∧ (0 : Coeff q) ∈ U ∧ U ⊆ T ∧
      (∀ φ : realTypeSourceSubmodule p, sourceActionSequence hp hp1 s φ.val ∈ U) ∧
      (∀ b : RealCoeff 1, (∀ n, 0 ≤ b n) →
        Coeff.exponentInclusion (Fact.out : 1 ≤ q) (RealCoeff.complexCLM 1 b) ∈ U) ∧
      ∃ Y : Set (CoeffPair p), IsOpen Y ∧ realTypeSourceLocus p ⊆ Y ∧ Y ⊆ V ∧
        sourceActionSequence (q := q) hp hp1 s '' Y = U := by
  obtain ⟨L,hL,hcenter,hlift⟩ := exists_sourceAction_openNeighborhood (q := q)
    hp hp1 V D.complex.source_open D.complex.real_subset
  have hrealL (φ : realTypeSourceSubmodule p) : sourceActionSequence (q := q) hp hp1 s φ.val ∈ L := by
    obtain ⟨a,ha,he⟩ := hcenter φ
    have heq : sourceActionSequence (q := q) hp hp1 s φ.val = a := by
      ext n
      exact (D.complex.actionSequence_apply φ.val (D.complex.real_subset φ.property) n).trans (he n).symm
    rwa [heq]
  have hcenter' (φ : realTypeSourceSubmodule p) : sourceActionSequence hp hp1 s φ.val ∈ T ∩ L :=
    ⟨hrealT φ,hrealL φ⟩
  let U := connectedComponentIn (T ∩ L) (0 : Coeff q)
  have hU : IsOpen U := (hT.inter hL).connectedComponentIn
  have hsub : U ⊆ T ∩ L := connectedComponentIn_subset _ _
  have hrU := D.complex.real_actions_mem_zero_component hcenter'
  have hz : (0 : Coeff q) ∈ U := by
    simpa only [ZeroMemClass.coe_zero,D.complex.actionSequence_zero] using hrU 0
  let Y := V ∩ sourceActionSequence (q := q) hp hp1 s ⁻¹' U
  refine ⟨U,hU,isPreconnected_connectedComponentIn,hz,fun _ hb => (hsub hb).1,hrU,?_,
    Y,D.complex.actionSequence_analytic.continuousOn.isOpen_inter_preimage D.complex.source_open hU,
    fun φ hφ => ⟨D.complex.real_subset hφ,hrU ⟨φ,hφ⟩⟩,inter_subset_left,?_⟩
  · intro b hb
    obtain ⟨φ,hφ⟩ := exists_source_of_nonnegative_actions hp hp1 h2p b hb
    have he : sourceActionSequence (q := q) hp hp1 s φ.val =
        Coeff.exponentInclusion (Fact.out : 1 ≤ q) (RealCoeff.complexCLM 1 b) := by
      ext n
      exact (D.complex.actionSequence_apply φ.val (D.complex.real_subset φ.property) n).trans (hφ n)
    rw [← he]
    exact hrU φ
  · apply Subset.antisymm
    · rintro _ ⟨φ,hφ,rfl⟩
      exact hφ.2
    · intro b hb
      obtain ⟨φ,hφ,he⟩ := hlift b (hsub hb).2
      have heq : sourceActionSequence (q := q) hp hp1 s φ = b := by
        ext n
        exact (D.complex.actionSequence_apply φ hφ n).trans (he n)
      exact ⟨φ,⟨hφ,show sourceActionSequence (q := q) hp hp1 s φ ∈ U from heq.symm ▸ hb⟩,heq⟩

end NLS.ZakharovShabat
