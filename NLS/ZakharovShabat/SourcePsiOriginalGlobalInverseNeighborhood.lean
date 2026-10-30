import NLS.SequenceSpaces.NearbyInverse
import NLS.ZakharovShabat.SourcePsiOriginalJointRealProjection
import NLS.ZakharovShabat.SourcePsiOriginalComplexInverseBounds

/-!
# Global original inverse neighborhoods

One simply connected complex neighborhood of the entire original real domain preserves the original isolating disks and locally common full and deleted inverse bounds.
-/

noncomputable section
namespace NLS.ZakharovShabat
open Set Complex Metric
open scoped ENNReal
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A single simply connected complex neighborhood of the entire
original real domain retains original placement and locally common
inverse bounds for every signed index. -/
theorem SourceProposition12_9Data.original_global_simplyConnected_inverseNeighborhood
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceProposition12_9Data hp hp1 W) (hW : IsOpen W)
    (hreal : realTypeSourceLocus p ⊆ W)
    (V : realTypeSourceSubmodule p → Set (CoeffPair p))
    (D : realTypeSourceSubmodule p → ℤ → Set ℂ)
    (c : realTypeSourceSubmodule p → ℝ)
    (hD : ∀ φ, SourceIsolatingNeighborhoods hp hp1 (V φ) (D φ) (c φ))
    (hVopen : ∀ φ, IsOpen (V φ)) (hV : ∀ φ, (φ:CoeffPair p) ∈ V φ) :
    ∃ U : Set (Coeff p × CoeffPair p), IsOpen U ∧ IsSimplyConnected U ∧
      sourcePsiOriginalRealEmbedding p '' (⋃ φ, sourcePsiOriginalOmega (V φ) (D φ)) ⊆ U ∧
      U ⊆ ⋃ φ, sourcePsiOriginalRootPlacement (D φ) ×ˢ (W ∩ V φ) ∧
      ∀ u ∈ U, ∃ O : Set (Coeff p × CoeffPair p), IsOpen O ∧ u ∈ O ∧ O ⊆ U ∧
        ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℤ, ∀ v ∈ O,
          ∃ R : Coeff p →L[ℂ] Coeff p,
            (sourcePsiOriginalFullRootJacobian hp hp1 n v.1 v.2).comp R = ContinuousLinearMap.id ℂ (Coeff p) ∧
            R.comp (sourcePsiOriginalFullRootJacobian hp hp1 n v.1 v.2) = ContinuousLinearMap.id ℂ (Coeff p) ∧
            ‖R‖ ≤ M := by
  classical
  let A := ⋃ φ, sourcePsiOriginalOmega (V φ) (D φ)
  let B : Set (Coeff p × CoeffPair p) := ⋃ φ, sourcePsiOriginalRootPlacement (D φ) ×ˢ (W ∩ V φ)
  have hlocal (t : A) :
      ∃ O : Set (Coeff p × CoeffPair p), IsOpen O ∧ sourcePsiOriginalRealEmbedding p t.val ∈ O ∧
        O ⊆ B ∧ ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℤ, ∀ v ∈ O,
          ∃ R : Coeff p →L[ℂ] Coeff p,
            (sourcePsiOriginalFullRootJacobian hp hp1 n v.1 v.2).comp R = ContinuousLinearMap.id ℂ (Coeff p) ∧
            R.comp (sourcePsiOriginalFullRootJacobian hp hp1 n v.1 v.2) = ContinuousLinearMap.id ℂ (Coeff p) ∧
            ‖R‖ ≤ M := by
    obtain ⟨φ,hφ⟩ := mem_iUnion.mp t.property
    obtain ⟨O,hO,htO,hOB,M,hM,hb⟩ := H.original_isolating_neighborhood_inverseBound hW
      (hD φ) (hVopen φ) t.val (hreal t.val.1.property) hφ
    exact ⟨O,hO,htO,fun v hv => mem_iUnion.mpr ⟨φ,hOB hv⟩,M,hM,hb⟩
  choose O hO hcenter hOB M hM hb using hlocal
  let G := ⋃ t : A, O t
  have hG : IsOpen G := isOpen_iUnion hO
  have hAG : sourcePsiOriginalRealEmbedding p '' A ⊆ G := by
    rintro _ ⟨t,ht,rfl⟩
    exact mem_iUnion.mpr ⟨⟨t,ht⟩,hcenter ⟨t,ht⟩⟩
  obtain ⟨U,hU,hAU,hUG,hcontract⟩ := exists_contractible_complex_neighborhood_originalOmega
    hp hp1 V D c hD hVopen hV G hG hAG
  let : ContractibleSpace U := hcontract
  refine ⟨U,hU,SimplyConnectedSpace.ofContractible U,hAU,?_,?_⟩
  · intro v hv
    obtain ⟨t,ht⟩ := mem_iUnion.mp (hUG hv)
    exact hOB t ht
  · intro v hv
    obtain ⟨t,ht⟩ := mem_iUnion.mp (hUG hv)
    exact ⟨O t ∩ U,(hO t).inter hU,⟨ht,hv⟩,fun _ hx => hx.2,M t,hM t,
      fun n x hx => hb t n x hx.1⟩

end NLS.ZakharovShabat

namespace NLS.ZakharovShabat
open Set Complex Metric
open scoped ENNReal
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The same global domain construction controls the original deleted
Jacobians with the unchanged full inverse bound. -/
theorem SourceProposition12_9Data.original_global_simplyConnected_deletedInverseNeighborhood
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceProposition12_9Data hp hp1 W) (hW : IsOpen W)
    (hreal : realTypeSourceLocus p ⊆ W)
    (V : realTypeSourceSubmodule p → Set (CoeffPair p))
    (D : realTypeSourceSubmodule p → ℤ → Set ℂ)
    (c : realTypeSourceSubmodule p → ℝ)
    (hD : ∀ φ, SourceIsolatingNeighborhoods hp hp1 (V φ) (D φ) (c φ))
    (hVopen : ∀ φ, IsOpen (V φ)) (hV : ∀ φ, (φ:CoeffPair p) ∈ V φ) :
    ∃ U : Set (Coeff p × CoeffPair p), IsOpen U ∧ IsSimplyConnected U ∧
      sourcePsiOriginalRealEmbedding p '' (⋃ φ, sourcePsiOriginalOmega (V φ) (D φ)) ⊆ U ∧
      U ⊆ ⋃ φ, sourcePsiOriginalRootPlacement (D φ) ×ˢ (W ∩ V φ) ∧
      ∀ u ∈ U, ∃ O : Set (Coeff p × CoeffPair p), IsOpen O ∧ u ∈ O ∧ O ⊆ U ∧
        ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℤ, ∀ v ∈ O,
          ∃ R : DeletedCoeff p n →L[ℂ] DeletedCoeff p n,
            (sourcePsiOriginalRootJacobian hp hp1 n (Coeff.deleteCoordinateTo n v.1) v.2).comp R =
              ContinuousLinearMap.id ℂ (DeletedCoeff p n) ∧
            R.comp (sourcePsiOriginalRootJacobian hp hp1 n (Coeff.deleteCoordinateTo n v.1) v.2) =
              ContinuousLinearMap.id ℂ (DeletedCoeff p n) ∧ ‖R‖ ≤ M := by
  obtain ⟨U,hU,hsc,hAU,hUB,hb⟩ := H.original_global_simplyConnected_inverseNeighborhood
    hW hreal V D c hD hVopen hV
  refine ⟨U,hU,hsc,hAU,hUB,?_⟩
  intro u hu
  obtain ⟨O,hO,huO,hOU,M,hM,hbound⟩ := hb u hu
  refine ⟨O,hO,huO,hOU,M,hM,?_⟩
  intro n v hv
  obtain ⟨S,hTS,hST,hS⟩ := hbound n v hv
  obtain ⟨R,hQR,hRQ,hR⟩ := Coeff.exists_deleted_inverse_of_extension_inverse n
    (sourcePsiOriginalRootJacobian hp hp1 n (Coeff.deleteCoordinateTo n v.1) v.2) S hTS hST
  exact ⟨R,hQR,hRQ,hR.trans hS⟩

end NLS.ZakharovShabat
