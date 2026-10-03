import NLS.SequenceSpaces.RealActionRotationOrbit
import NLS.ZakharovShabat.SourceHilbertActionRotation

/-! # Lemma 17.5: the images of actual isospectral sets

Finite action rotations are dense in each Hilbert coordinate torus.
Their lifted sources are isospectral; continuity of the inverse and
closedness of the actual isospectral set give the converse inclusion.
Action and discriminant compatibility transfer the result to every
`1 < p ≤ 2`. Thus actual isospectral sets are exactly original action
level sets in this range and map onto the whole compact action torus.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat

namespace SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)} {s : (k : ℤ) → CoeffPair 2 → DeletedCoeff 2 k}

/-- Equal Hilbert actions imply actual isospectrality, including infinitely many open gaps. -/
theorem hilbert_actionLevelSet_subset_isospectralSet
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) :
    sourceRealActionLevelSet (by simp) (by norm_num) φ ⊆ sourceIsospectralSet (by simp) φ := by
  intro ψ hψ
  let C : Set (RealCoeff 2 × RealCoeff 2) :=
    D.hilbertRealHomeomorph.symm ⁻¹' sourceIsospectralSet (by simp) φ
  have hC : IsClosed C := (isClosed_sourceIsospectralSet (by simp) (by norm_num) φ).preimage
    D.hilbertRealHomeomorph.symm.continuous
  have horbit : range (RealCoeff.actionRotationSequence (D.hilbertRealHomeomorph φ)) ⊆ C := by
    rintro _ ⟨moves,rfl⟩
    have he : D.hilbertRealHomeomorph.symm
        (RealCoeff.actionRotationSequence (D.hilbertRealHomeomorph φ) moves) =
        D.hilbertActionRotationSequence φ moves := by
      apply D.hilbertRealHomeomorph.injective
      rw [D.hilbertRealHomeomorph.apply_symm_apply,D.hilbertRealHomeomorph_actionRotationSequence]
      rfl
    change D.hilbertRealHomeomorph.symm _ ∈ sourceIsospectralSet (by simp) φ
    rw [he]
    exact D.hilbertActionRotationSequence_mem_isospectralSet φ moves
  have hclosure := closure_minimal horbit hC
  have hy : D.hilbertRealHomeomorph ψ ∈
      closure (range (RealCoeff.actionRotationSequence (D.hilbertRealHomeomorph φ))) := by
    rw [RealCoeff.closure_actionRotationSequence_range (by simp)]
    intro n
    rw [D.hilbert_pairAction_eq,D.hilbert_pairAction_eq]
    exact hψ n
  have hm := hclosure hy
  change D.hilbertRealHomeomorph.symm (D.hilbertRealHomeomorph ψ) ∈ sourceIsospectralSet (by simp) φ at hm
  simpa only [D.hilbertRealHomeomorph.symm_apply_apply] using hm

end SourceBirkhoffMapComplexData

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Equal original actions imply equality of the original spectrum and multiplicities
throughout `1 < p ≤ 2`; the Hilbert normalized family is constructed internally. -/
theorem sourceRealActionLevelSet_subset_isospectralSet (hp : p ≠ ⊤) (hp1 : 1 < p)
    (hp2 : p ≤ 2) (φ : realTypeSourceSubmodule p) :
    sourceRealActionLevelSet hp hp1 φ ⊆ sourceIsospectralSet hp φ := by
  intro ψ hψ
  obtain ⟨V₀,C,V,u,E⟩ := exists_sourceBirkhoffMap_complex_analytic (p := 2) (by simp) (by norm_num)
  let φ₂ : realTypeSourceSubmodule 2 := realTypeSourceExponentInclusion hp2 φ
  let ψ₂ : realTypeSourceSubmodule 2 := realTypeSourceExponentInclusion hp2 ψ
  have ha : ψ₂ ∈ sourceRealActionLevelSet (by simp) (by norm_num) φ₂ := by
    intro n
    have hx := congrArg Complex.re (sourceRealAction_exponent hp (by simp) hp1 (by norm_num) hp2 n ψ)
    have hy := congrArg Complex.re (sourceRealAction_exponent hp (by simp) hp1 (by norm_num) hp2 n φ)
    exact hx.symm.trans ((hψ n).trans hy)
  have hiso := E.hilbert_actionLevelSet_subset_isospectralSet φ₂ ha
  have hΔ := (mem_sourceIsospectralSet_iff_discriminant_eq (by simp) (by norm_num) φ₂ ψ₂).mp hiso
  apply (mem_sourceIsospectralSet_iff_discriminant_eq hp hp1 φ ψ).mpr
  funext z
  exact (sourceDiscriminant_exponent hp (by simp) hp2 ψ.val z).trans
    ((congrFun hΔ z).trans (sourceDiscriminant_exponent hp (by simp) hp2 φ.val z).symm)

/-- Actual isospectral sets coincide with the level sets of all original actions. -/
theorem sourceIsospectralSet_eq_actionLevelSet (hp : p ≠ ⊤) (hp1 : 1 < p)
    (hp2 : p ≤ 2) (φ : realTypeSourceSubmodule p) :
    sourceIsospectralSet hp φ = sourceRealActionLevelSet hp hp1 φ :=
  Subset.antisymm (sourceIsospectralSet_subset_actionLevelSet hp hp1 φ)
    (sourceRealActionLevelSet_subset_isospectralSet hp hp1 hp2 φ)

namespace SourceBirkhoffMapComplexData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}

/-- Lemma 17.5(i): the full actual isospectral image is the prescribed action torus. -/
theorem image_isospectralSet_eq_actionTorus
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (hp2 : p ≤ 2)
    (φ : realTypeSourceSubmodule p) :
    sourceRealBirkhoffMap hp hp1 s '' sourceIsospectralSet hp φ =
      RealCoeff.actionTorus p (fun n => (sourceRealAction hp hp1 φ.val φ.property n).re) := by
  rw [sourceIsospectralSet_eq_actionLevelSet hp hp1 hp2]
  exact D.image_actionLevelSet_eq_actionTorus hp2 φ

/-- Both assertions of Lemma 17.5(i), with compactness in the original source norm. -/
theorem lemma17_5_i
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (hp2 : p ≤ 2)
    (φ : realTypeSourceSubmodule p) :
    sourceRealBirkhoffMap hp hp1 s '' sourceIsospectralSet hp φ =
        RealCoeff.actionTorus p (fun n => (sourceRealAction hp hp1 φ.val φ.property n).re) ∧
      IsCompact (sourceIsospectralSet hp φ) :=
  ⟨D.image_isospectralSet_eq_actionTorus hp2 φ,D.isCompact_isospectralSet hp2 φ⟩

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
