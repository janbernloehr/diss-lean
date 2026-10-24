import NLS.ZakharovShabat.SymmetricSignedGapFiniteCompactness
import NLS.ZakharovShabat.SymmetricSignedGapKernelVanishing
import NLS.FunctionalAnalysis.LocalHomeomorphRestriction
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-! # Properness over each finite signed-gap output space

The finite coordinate space is a real normed subspace. Restricting the
actual Hilbert signed-gap map to its full preimage gives a proper local
homeomorphism onto this space. Properness follows from compactness of
preimages in the original source norm.
-/
noncomputable section
open Set Complex Topology
namespace NLS.ZakharovShabat

/-- Real Hilbert sequences supported in a prescribed finite set. -/
def finiteSignedGapOutputSpace (S : Finset ℤ) : Submodule ℝ (RealCoeff 2) where
  carrier := {y | ∀ n ∉ S, y n = 0}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb n hn
    change a n + b n = 0
    rw [ha n hn,hb n hn,add_zero]
  smul_mem' := by
    intro c a ha n hn
    change c * a n = 0
    rw [ha n hn,mul_zero]

/-- The actual signed-gap map with finite-support target and its full preimage as source. -/
def symmetricSignedGapFiniteRestriction (S : Finset ℤ) :
    {a : RealCoeff 2 | symmetricSourceSignedGapMap (by simp) (by norm_num) a ∈
      finiteSignedGapOutputSpace S} → finiteSignedGapOutputSpace S :=
  (finiteSignedGapOutputSpace S : Set (RealCoeff 2)).restrictPreimage
    (symmetricSourceSignedGapMap (by simp) (by norm_num))

/-- Actual derivative bijectivity gives local homeomorphisms at every Hilbert source. -/
theorem isLocalHomeomorph_symmetricSourceSignedGapMap :
    IsLocalHomeomorph (symmetricSourceSignedGapMap (p := 2) (by simp) (by norm_num)) := by
  intro a
  obtain ⟨e,he⟩ := exists_equiv_fderiv_symmetricSourceSignedGapMap_of_injective a
    (bijective_fderiv_symmetricSourceSignedGapMap a).1
  have hs := (analyticAt_symmetricSourceSignedGapMap (p := 2)
    (by simp) (by norm_num) a).contDiffAt.hasStrictFDerivAt (n := 1) one_ne_zero
  rw [← he] at hs
  exact ⟨hs.toOpenPartialHomeomorph _,hs.mem_toOpenPartialHomeomorph_source,rfl⟩

/-- Restriction to finite output support preserves the actual local homeomorphism. -/
theorem isLocalHomeomorph_symmetricSignedGapFiniteRestriction (S : Finset ℤ) :
    IsLocalHomeomorph (symmetricSignedGapFiniteRestriction S) :=
  NLS.FunctionalAnalysis.isLocalHomeomorph_restrictPreimage
    isLocalHomeomorph_symmetricSourceSignedGapMap (finiteSignedGapOutputSpace S)

/-- The actual signed-gap map is proper over every finite output space. -/
theorem isProperMap_symmetricSignedGapFiniteRestriction (S : Finset ℤ) :
    IsProperMap (symmetricSignedGapFiniteRestriction S) := by
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨(isLocalHomeomorph_symmetricSignedGapFiniteRestriction S).continuous,?_⟩
  intro K hK
  have hc := isCompact_symmetricSignedGap_preimage_of_finite_support S
    (Subtype.val '' K) (hK.image continuous_subtype_val)
    (by rintro y ⟨z,_,rfl⟩; exact z.property)
  apply Subtype.isCompact_iff.mpr
  have he : Subtype.val '' ((symmetricSignedGapFiniteRestriction S) ⁻¹' K) =
      (symmetricSourceSignedGapMap (by simp) (by norm_num)) ⁻¹' (Subtype.val '' K) := by
    ext a
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨symmetricSignedGapFiniteRestriction S x,hx,rfl⟩
    · rintro ⟨y,hy,heq⟩
      have hmem : symmetricSourceSignedGapMap (by simp) (by norm_num) a ∈
          finiteSignedGapOutputSpace S := by
        rw [← heq]
        exact y.property
      refine ⟨⟨a,hmem⟩,?_,rfl⟩
      change symmetricSignedGapFiniteRestriction S ⟨a,hmem⟩ ∈ K
      have h : symmetricSignedGapFiniteRestriction S ⟨a,hmem⟩ = y := Subtype.ext heq.symm
      rw [h]
      exact hy
  rw [he]
  exact hc

end NLS.ZakharovShabat
