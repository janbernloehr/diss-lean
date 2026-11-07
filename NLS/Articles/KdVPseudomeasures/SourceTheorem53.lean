import NLS.Articles.KdVPseudomeasures.SourceTheorem53SpectralBound
import NLS.Articles.KdVPseudomeasures.MainTheorem51
import NLS.Articles.KdVPseudomeasures.OriginalHillGlobalNativeInverse

/-! Theorem 5.3 from the literal gap-only regularity hypothesis. The
proof retains the original distribution and every member of its entire
H-minus-one isospectral set. -/
noncomputable section
open Set Complex NLS.KdV NLS.WeightedCoeff
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures

private theorem source53_weighted_membership (N : ℕ) (z g : ℤ → ℂ)
    (hg : Memℓp (fun k => (Weight.signedSobolev (N:ℝ) k:ℂ)*g k) 1)
    (C : ℝ) (hb : ∀ k, ‖(Weight.signedSobolev (1/2) k:ℂ)*z k‖ ≤ C*‖g k‖) :
    Memℓp (fun k => (Weight.signedSobolev ((N:ℝ)+1/2) k:ℂ)*z k) 1 := by
  apply (hg.norm.const_mul C).mono
  intro k
  have hw : Weight.signedSobolev ((N:ℝ)+1/2) k=
      Weight.signedSobolev (N:ℝ) k*Weight.signedSobolev (1/2) k :=
    Real.rpow_add (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) _ _
  have h := mul_le_mul_of_nonneg_left (hb k) ((Weight.signedSobolev (N:ℝ)).positive k).le
  simp only [norm_mul,Complex.norm_real,
    Real.norm_of_nonneg ((Weight.signedSobolev (1/2)).positive k).le] at h
  rw [norm_mul,Complex.norm_real,
    Real.norm_of_nonneg ((Weight.signedSobolev ((N:ℝ)+1/2)).positive k).le,hw]
  calc
    _ = Weight.signedSobolev (N:ℝ) k*(Weight.signedSobolev (1/2) k*‖z k‖) := by ring
    _ ≤ Weight.signedSobolev (N:ℝ) k*(C*‖g k‖) := h
    _ = _ := by
      rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg ((Weight.signedSobolev (N:ℝ)).positive k).le]
      ring

theorem exists_originalWiener_target_of_gap_membership (N : ℕ) (q : OriginalHminusOnePotential)
    (hg : Memℓp (fun k => (Weight.signedSobolev (N:ℝ) k:ℂ)*originalCanonicalGapValues q k) 1) :
    ∃ z : OriginalWienerTarget N, ∀ k,
      z.val.val.val k=hillHminusNativeCoordinate k (originalPeriodOneCoefficients q) := by
  obtain ⟨C,_,hb⟩ := original_native_signed_half_gap_bound q
  let Z := hillHminusNativeComplexMap (originalPeriodOneCoefficients q)
  have hm := source53_weighted_membership N Z.val (originalCanonicalGapValues q) hg C hb
  rw [← originalWienerTarget_order N] at hm
  let a : WeightedCoeff (Weight.signedSobolev (signedStepOrder (1/2) N)) 1 := ⟨Z.val,hm⟩
  let z : fourierRealZeroSubmodule (Weight.signedSobolev (signedStepOrder (1/2) N)) 1 :=
    ⟨⟨a,hillHminusNativeComplexMap_zero_mode _⟩,
      hillHminusNativeComplexMap_real _ (originalPeriodOneCoefficients_real q)⟩
  refine ⟨(originalWienerTargetCoefficients N).symm z,?_⟩
  intro k
  exact originalWienerTargetCoefficients_symm_apply N z k

/-- Actual native target regularity gives the same original physical
Wiener potential, by the proved global Wiener inverse and rough injectivity. -/
theorem exists_originalWiener_of_native_target (N : ℕ) (q : OriginalHminusOnePotential)
    (z : OriginalWienerTarget N)
    (hz : ∀ k, z.val.val.val k=hillHminusNativeCoordinate k (originalPeriodOneCoefficients q)) :
    ∃ p : OriginalWienerPotential N, originalWienerOriginalPotential N p=q := by
  let p := (originalHillWienerEquiv N).symm z
  have hp : originalHillWienerEquiv N p=z := (originalHillWienerEquiv N).apply_symm_apply z
  have hmap : hillRealSignedMap (originalHillRealMeanZeroSource (originalWienerOriginalPotential N p))=
      hillRealSignedMap (originalHillRealMeanZeroSource q) := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    funext k
    calc
      _ = (originalHillWienerEquiv N p).val.val.val k := (originalHillWienerEquiv_apply N p k).symm
      _ = z.val.val.val k := congrArg (fun a : OriginalWienerTarget N => a.val.val.val k) hp
      _ = hillHminusNativeCoordinate k (originalPeriodOneCoefficients q) := hz k
      _ = _ := by rw [hillRealSignedMap_coordinate,originalHillRealMeanZeroSource_inclusion]
  have hsource := injective_hillRealSignedMap hmap
  have hphysical := congrArg originalHillPotentialOfRealSource hsource
  rw [originalHillPotentialOfRealSource_ofOriginal,originalHillPotentialOfRealSource_ofOriginal] at hphysical
  exact ⟨p,hphysical⟩

/-- The gap-only inverse regularity assertion on the entire rough real
source. In particular it applies to every real mean-zero L2 potential. -/
theorem sourceTheorem5_3_signed (N : ℕ) (q : OriginalHminusOnePotential)
    (hg : Memℓp (fun k => (Weight.signedSobolev (N:ℝ) k:ℂ)*originalCanonicalGapValues q k) 1) :
    (∃ p : OriginalWienerPotential N, originalWienerOriginalPotential N p=q) ∧
      ∀ v : OriginalHminusOnePotential, v ∈ originalIsospectralSet q →
        ∃ p : OriginalWienerPotential N, originalWienerOriginalPotential N p=v := by
  have hreg (v : OriginalHminusOnePotential)
      (hv : Memℓp (fun k => (Weight.signedSobolev (N:ℝ) k:ℂ)*originalCanonicalGapValues v k) 1) :
      ∃ p : OriginalWienerPotential N, originalWienerOriginalPotential N p=v := by
    obtain ⟨z,hz⟩ := exists_originalWiener_target_of_gap_membership N v hv
    exact exists_originalWiener_of_native_target N v z hz
  refine ⟨hreg q hg,?_⟩
  intro v hv
  apply hreg
  rw [originalCanonicalGapValues_isospectral q v hv]
  exact hg

end NLS.Articles.KdVPseudomeasures
