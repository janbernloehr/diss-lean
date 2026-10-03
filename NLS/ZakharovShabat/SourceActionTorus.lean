import NLS.SequenceSpaces.RealActionTorus
import NLS.ZakharovShabat.SourceBirkhoffGlobalInverse

/-! # Original spectral action level sets and compact coordinate tori

The actual Birkhoff map identifies its source action level sets with
coordinate action tori whenever `1 < p ≤ 2`. The global homeomorphism
therefore makes these level sets compact in the original source norm.
Identifying these sets with the actual isospectral sets is a subsequent
step of Lemma 17.5, not an assumption of the results here.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Sources with the same original spectral actions as a given real source. -/
def sourceRealActionLevelSet (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) : Set (realTypeSourceSubmodule p) :=
  {ψ | ∀ n : ℤ, (sourceRealAction hp hp1 ψ.val ψ.property n).re =
    (sourceRealAction hp hp1 φ.val φ.property n).re}

namespace SourceBirkhoffMapComplexData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}

/-- The quadratic output action is the original source action at every exponent. -/
theorem real_pairAction_eq (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (φ : realTypeSourceSubmodule p) (n : ℤ) :
    RealCoeff.pairAction (sourceRealBirkhoffMap hp hp1 s φ) n =
      (sourceRealAction hp hp1 φ.val φ.property n).re := by
  dsimp only [RealCoeff.pairAction]
  rw [D.real_map_action_radius]
  ring

/-- The preimage of the action torus is exactly the original action level set. -/
theorem actionLevelSet_eq_preimage_actionTorus
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (φ : realTypeSourceSubmodule p) :
    sourceRealActionLevelSet hp hp1 φ =
      (sourceRealBirkhoffMap hp hp1 s) ⁻¹' RealCoeff.actionTorus p
        (fun n => (sourceRealAction hp hp1 φ.val φ.property n).re) := by
  ext ψ
  simp only [sourceRealActionLevelSet,RealCoeff.actionTorus,mem_ofPred_eq,mem_preimage,D.real_pairAction_eq]

/-- Source action level sets are closed for all finite exponents above one. -/
theorem isClosed_actionLevelSet (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (φ : realTypeSourceSubmodule p) : IsClosed (sourceRealActionLevelSet hp hp1 φ) := by
  rw [D.actionLevelSet_eq_preimage_actionTorus]
  exact (RealCoeff.isClosed_actionTorus _).preimage D.real_map_isOpenEmbedding.continuous

/-- All source action level sets map into the prescribed coordinate torus. -/
theorem image_actionLevelSet_subset_actionTorus
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (φ : realTypeSourceSubmodule p) :
    sourceRealBirkhoffMap hp hp1 s '' sourceRealActionLevelSet hp hp1 φ ⊆
      RealCoeff.actionTorus p (fun n => (sourceRealAction hp hp1 φ.val φ.property n).re) := by
  rintro _ ⟨ψ,hψ,rfl⟩ n
  exact (D.real_pairAction_eq ψ n).trans (hψ n)

/-- For exponents at most two, every point of the prescribed action torus
has an original real source with exactly those actions. -/
theorem image_actionLevelSet_eq_actionTorus
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (hp2 : p ≤ 2)
    (φ : realTypeSourceSubmodule p) :
    sourceRealBirkhoffMap hp hp1 s '' sourceRealActionLevelSet hp hp1 φ =
      RealCoeff.actionTorus p (fun n => (sourceRealAction hp hp1 φ.val φ.property n).re) := by
  apply Subset.antisymm (D.image_actionLevelSet_subset_actionTorus φ)
  intro z hz
  obtain ⟨ψ,hψ⟩ := D.proposition17_3 hp2 z
  refine ⟨ψ,?_,hψ⟩
  intro n
  rw [← D.real_pairAction_eq ψ n,hψ]
  exact hz n

/-- Original spectral action level sets are compact in the full source norm
for `1 < p ≤ 2`, including sources with infinitely many open gaps. -/
theorem isCompact_actionLevelSet
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (hp2 : p ≤ 2)
    (φ : realTypeSourceSubmodule p) : IsCompact (sourceRealActionLevelSet hp hp1 φ) := by
  rw [D.actionLevelSet_eq_preimage_actionTorus]
  exact (D.realHomeomorph hp2).isCompact_preimage.mpr (RealCoeff.isCompact_actionTorus hp _)

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
