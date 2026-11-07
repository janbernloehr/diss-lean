import NLS.Articles.KdVPseudomeasures.OriginalEndpointBound
import NLS.Articles.KdVPseudomeasures.OriginalHminusOneCompactness
import NLS.Articles.KdVPseudomeasures.SourceWeakStarTopology
import NLS.Articles.KdVPseudomeasures.SpectralClosedFibers

/-!
# Theorem 2.2(iii): weak-star compactness of the entire original isospectral set

The endpoint set contains precisely the representatives of the full original
H-minus-one isospectral family. Lemma 2.21 supplies its uniform original
endpoint norm bound. Its lower H-minus-one image is exactly the original
norm-compact family, so Appendix B applies with no extra compactness premise.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

/-- Exact target weak-star representatives of the ENTIRE original isospectral
family. Membership identifies entire distributions, not only spectral data. -/
def originalIsospectralEndpointSet (q : OriginalHminusOnePotential) (r : ℝ) :
    Set (WeakStarPotential r) :=
  {a | ∃ v ∈ originalIsospectralSet q, a.toPotential.val.val = v.val.val}

/-- Endpoint-set membership is exactly original physical isospectrality,
without any gap hypothesis or chosen representative. -/
theorem mem_originalIsospectralEndpointSet_iff (q : OriginalHminusOnePotential)
    (r : ℝ) (hr : AdmissiblePredualOrder r) (a : WeakStarPotential r) :
    a ∈ originalIsospectralEndpointSet q r ↔
      sourceOriginalPotential r hr a.toPotential ∈ originalIsospectralSet q := by
  constructor
  · rintro ⟨v,hv,hval⟩
    have he : sourceOriginalPotential r hr a.toPotential = v := by
      apply Subtype.ext
      apply Subtype.ext
      exact (sourceOriginalPotential_val r hr a.toPotential).trans hval
    exact he.symm ▸ hv
  · intro ha
    exact ⟨sourceOriginalPotential r hr a.toPotential,ha,
      (sourceOriginalPotential_val r hr a.toPotential).symm⟩

/-- The exact endpoint set is the full intrinsic canonical spectral fiber,
retaining the entire ordered list and all algebraic repetitions. -/
theorem originalIsospectralEndpointSet_eq_spectralFiber (q : OriginalHminusOnePotential)
    (r : ℝ) (hr : AdmissiblePredualOrder r) :
    originalIsospectralEndpointSet q r = sourceCanonicalSpectralFiber r hr (originalHillLabels q) := by
  ext a
  rw [mem_originalIsospectralEndpointSet_iff q r hr a,
    mem_originalIsospectralSet_iff_originalHillLabels,originalHillLabels_sourceOriginalPotential]
  rfl

/-- Lemma 2.21 gives norm boundedness of the exact original endpoint set. -/
theorem potentialNormBounded_originalIsospectralEndpointSet
    (q : OriginalHminusOnePotential) (r : ℝ) (hr : AdmissiblePredualOrder r)
    (hgap : Memℓp (fun n : ℤ => (Weight.sobolev (-r) n:ℂ)*originalCanonicalGapValues q n) ⊤) :
    PotentialNormBounded r (originalIsospectralEndpointSet q r) := by
  obtain ⟨C,_,hC⟩ := sourceLemma2_21 q r hr hgap
  refine ⟨C,?_⟩
  rintro a ⟨v,hv,hav⟩
  obtain ⟨b,hb,hbn⟩ := hC v hv
  have he : a.toPotential.val = b.val := Subtype.ext (hav.trans hb.symm)
  simpa only [he] using hbn

/-- The lower realization of the full endpoint set is EXACTLY the original
H-minus-one isospectral distribution family, including every member. -/
theorem sourceLowerDistribution_originalIsospectralEndpointSet
    (q : OriginalHminusOnePotential) (r : ℝ) (hr : AdmissiblePredualOrder r)
    (hgap : Memℓp (fun n : ℤ => (Weight.sobolev (-r) n:ℂ)*originalCanonicalGapValues q n) ⊤) :
    sourceLowerDistribution r (-1) (p := 2) (by norm_num)
      (admissible_hminusOne_threshold r hr) '' originalIsospectralEndpointSet q r =
        Subtype.val '' originalIsospectralSet q := by
  ext Q
  constructor
  · rintro ⟨a,⟨v,hv,hav⟩,rfl⟩
    refine ⟨v,hv,?_⟩
    apply Subtype.ext
    rw [sourceLowerDistribution_val]
    exact hav.symm
  · rintro ⟨v,hv,rfl⟩
    obtain ⟨a,ha⟩ := sourceTheorem2_2_ii q r hr hgap v hv
    refine ⟨⟨a⟩,⟨v,hv,ha⟩,?_⟩
    apply Subtype.ext
    rw [sourceLowerDistribution_val]
    exact ha

/-- Source Theorem 2.2(iii), on its full original H-minus-one domain and
with the exact original endpoint weak-star topology. The only regularity
hypothesis concerns the actual original spectral gaps. -/
theorem sourceTheorem2_2_iii (q : OriginalHminusOnePotential)
    (r : ℝ) (hr : AdmissiblePredualOrder r)
    (hgap : Memℓp (fun n : ℤ => (Weight.sobolev (-r) n:ℂ)*originalCanonicalGapValues q n) ⊤) :
    IsCompact (originalIsospectralEndpointSet q r) := by
  apply (isCompact_source_iff_bounded_lower_compact r (-1) (p := 2) (by norm_num)
    (admissible_hminusOne_threshold r hr) _).mpr
  refine ⟨potentialNormBounded_originalIsospectralEndpointSet q r hr hgap,?_⟩
  rw [sourceLowerDistribution_originalIsospectralEndpointSet q r hr hgap]
  exact (isCompact_originalIsospectralSet q).image continuous_subtype_val

end NLS.Articles.KdVPseudomeasures
