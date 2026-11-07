import NLS.Articles.KdVPseudomeasures.OriginalIsospectralMiura
import NLS.KdV.HminusOneMiuraCompactness
import NLS.Fourier.PeriodicPhysicalSourceClosed

/-!
# Norm compactness of the entire original H-minus-one isospectral set

The exact physical discriminant makes the full original isospectral set
closed. All its members are covered by a compact shifted real Miura image
of one actual Dirac isospectral set. No endpoint membership or endpoint norm
bound is assumed, and no stronger norm compactness is inferred.
-/
noncomputable section
open Set
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV NLS.ZakharovShabat NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

/-- The original potential domain carries the subspace topology of its
unchanged original H-minus-one normed distribution space. -/
instance : TopologicalSpace OriginalHminusOnePotential :=
  inferInstanceAs (TopologicalSpace {q : FourierLebesgueSpace (2:ℝ) (-1) 2 //
    q.val.IsRealMeanZeroPeriodOne})

/-- The actual original discriminant depends continuously on the entire
original H-minus-one potential at every fixed complex energy. -/
theorem continuous_originalHillDiscriminant_potential (z : ℂ) :
    Continuous (fun q : OriginalHminusOnePotential => originalHillDiscriminant q z) :=
  (continuous_hillHminusDiscriminant_potential z).comp
    (periodOneOriginalExtract.continuous.comp continuous_subtype_val)

/-- The full original isospectral set is closed in the original H-minus-one norm. -/
theorem isClosed_originalIsospectralSet (q : OriginalHminusOnePotential) :
    IsClosed (originalIsospectralSet q) := by
  have he : originalIsospectralSet q =
      ⋂ z : ℂ, {p : OriginalHminusOnePotential |
        originalHillDiscriminant p z = originalHillDiscriminant q z} := by
    ext p
    rw [mem_originalIsospectralSet_iff_discriminant_eq]
    simp only [mem_iInter,mem_ofPred_eq,funext_iff]
  rw [he]
  exact isClosed_iInter fun z =>
    isClosed_eq (continuous_originalHillDiscriminant_potential z) continuous_const

/-- The entire original physical source domain is a closed subspace of its
original H-minus-one normed distribution space. -/
theorem isClosedEmbedding_originalHminusOnePotential :
    Topology.IsClosedEmbedding (Subtype.val : OriginalHminusOnePotential →
      FourierLebesgueSpace (2:ℝ) (-1) 2) :=
  (isClosed_realMeanZeroPeriodOneSource (-1) 2).isClosedEmbedding_subtypeVal

/-- The ENTIRE original isospectral set is compact in the original H-minus-one
norm, with no endpoint-space premise and no free Birkhoff-data assumption. -/
theorem isCompact_originalIsospectralSet (q : OriginalHminusOnePotential) :
    IsCompact (originalIsospectralSet q) := by
  obtain ⟨c,_,_,u₀,_,R,_,hlift⟩ :=
    exists_originalIsospectral_lifts_in_one_dirac_isospectral_set q 0
  let K := (fun v : PeriodOneRealL2 => periodOneMiura v.val-
      periodOneL2Inclusion (lp.single 2 0 ((c:ℂ)^2))) ''
        (hillMiuraRealSource ⁻¹' sourceIsospectralSet (by norm_num) (hillMiuraRealSource u₀))
  have hK : IsCompact (periodOneOriginal '' K) :=
    (isCompact_shiftedMiura_image_of_dirac_isospectral u₀ ((c:ℂ)^2)).image
      periodOneOriginal.continuous
  have hsub : (Subtype.val '' originalIsospectralSet q) ⊆ periodOneOriginal '' K := by
    rintro _ ⟨p,hp,rfl⟩
    obtain ⟨u,_,himage,hiso⟩ := hlift p hp
    refine ⟨periodOneMiura u.val-periodOneL2Inclusion (lp.single 2 0 ((c:ℂ)^2)),
      ⟨u,hiso,rfl⟩,?_⟩
    have he : periodOneMiura u.val-periodOneL2Inclusion (lp.single 2 0 ((c:ℂ)^2)) =
        originalPeriodOneCoefficients p := by rw [himage]; abel
    rw [he]
    exact periodOneOriginal_originalPeriodOneCoefficients p
  have hclosed := isClosedEmbedding_originalHminusOnePotential.isClosedMap
    (originalIsospectralSet q) (isClosed_originalIsospectralSet q)
  exact isClosedEmbedding_originalHminusOnePotential.isEmbedding.isCompact_iff.mpr
    (hK.of_isClosed_subset hclosed hsub)

end NLS.Articles.KdVPseudomeasures
