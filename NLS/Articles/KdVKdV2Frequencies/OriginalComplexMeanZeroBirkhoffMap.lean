import NLS.Articles.KdVKdV2Frequencies.GlobalRawSobolevDiffeomorphisms
import NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianComplexCanonical
import NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianOrigin
import NLS.Poisson.MeanZeroHminusGardnerBracket

/-! # The same original Birkhoff map in the actual complex mean-zero spaces -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology NLS.KdV
namespace NLS.Articles.KdVKdV2Frequencies

abbrev OriginalComplexBirkhoffSource := complexMeanZeroWeightedSubmodule (Weight.sobolev (-1))
abbrev OriginalComplexBirkhoffTarget := complexMeanZeroWeightedSubmodule (Weight.sobolev (-1/2))

/-- Literal signed coordinate of a map between the raw complex mean-zero spaces. -/
def originalMeanZeroBirkhoffComponent
    (Φ : OriginalComplexBirkhoffSource → OriginalComplexBirkhoffTarget)
    (σ : Bool) (n : ℕ+) (q : OriginalComplexBirkhoffSource) : ℂ :=
  (Φ q).val.val (if σ then (n : ℤ) else -(n : ℤ))

namespace GlobalRoughAbelianForwardData

/-- One open neighborhood inside the original closed complex mean-zero source. -/
def originalMeanZeroDomain (D : GlobalRoughAbelianForwardData) : Set OriginalComplexBirkhoffSource :=
  Subtype.val ⁻¹' D.canonicalDomain

/-- The actual original map with mean-zero source AND target types. -/
def originalMeanZeroMap (D : GlobalRoughAbelianForwardData) :
    OriginalComplexBirkhoffSource → OriginalComplexBirkhoffTarget :=
  fun q => complexMeanZeroWeightedProjection (Weight.sobolev (-1/2)) (D.signed q.val)

theorem originalMeanZeroDomain_open (D : GlobalRoughAbelianForwardData) :
    IsOpen D.originalMeanZeroDomain := D.canonicalDomain_open.preimage continuous_subtype_val

theorem real_mem_originalMeanZeroDomain (D : GlobalRoughAbelianForwardData)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (-1))) :
    physicalRealToComplexMeanZeroWeighted _ q ∈ D.originalMeanZeroDomain :=
  D.real_meanZero_mem_canonicalDomain q.val q.property.1 q.property.2

theorem originalMeanZeroMap_val (D : GlobalRoughAbelianForwardData)
    (q : OriginalComplexBirkhoffSource) (hq : q ∈ D.originalMeanZeroDomain) :
    (D.originalMeanZeroMap q).val = D.signed q.val :=
  WeightedCoeff.meanZeroWeightedLift_projection _ _
    (D.signed_zero q.val (D.canonicalDomain_subset_domain hq))

theorem originalMeanZeroMap_analytic (D : GlobalRoughAbelianForwardData) :
    AnalyticOnNhd ℂ D.originalMeanZeroMap D.originalMeanZeroDomain := by
  intro q hq
  exact ((complexMeanZeroWeightedProjection (Weight.sobolev (-1/2))).analyticAt _).comp
    ((D.signed_analytic q.val (D.canonicalDomain_subset_domain hq)).comp
      ((complexMeanZeroWeightedSubmodule (Weight.sobolev (-1))).subtypeL.analyticAt q))

theorem originalMeanZeroMap_zero (D : GlobalRoughAbelianForwardData) :
    D.originalMeanZeroMap 0 = 0 := by
  change complexMeanZeroWeightedProjection _ (D.signed 0) = 0
  rw [D.signed_at_origin,map_zero]

/-- Each literal nonzero coordinate has the original actual ambient extension. -/
theorem originalMeanZeroMap_component (D : GlobalRoughAbelianForwardData)
    (σ : Bool) (n : ℕ+) (q : OriginalComplexBirkhoffSource) :
    originalMeanZeroBirkhoffComponent D.originalMeanZeroMap σ n q =
      hillRoughSignedAbelianComponent D.signed σ n q.val := by
  apply complexMeanZeroWeightedProjection_apply_other
  cases σ <;> simp [Nat.ne_of_gt n.pos]

/-- The intrinsic Gardner matrix of the SAME map on the SAME complex neighborhood. -/
theorem originalMeanZeroMap_gardner_matrix (D : GlobalRoughAbelianForwardData)
    (q : OriginalComplexBirkhoffSource) (hq : q ∈ D.originalMeanZeroDomain)
    (σ τ : Bool) (n m : ℕ+) :
    NLS.Poisson.meanZeroHminusGardnerBracket
      (originalMeanZeroBirkhoffComponent D.originalMeanZeroMap σ n)
      (originalMeanZeroBirkhoffComponent D.originalMeanZeroMap τ m) q =
        hillOriginalComplexGardnerMatrixEntry σ τ n m/2 := by
  have he (b : Bool) (j : ℕ+) :
      (fun u => originalMeanZeroBirkhoffComponent D.originalMeanZeroMap b j
        (complexMeanZeroWeightedProjection (Weight.sobolev (-1)) u)) =
        fun u => hillRoughSignedAbelianComponent D.signed b j (hminusMeanZeroProjection u) := by
    funext u
    exact D.originalMeanZeroMap_component b j _
  unfold NLS.Poisson.meanZeroHminusGardnerBracket
  rw [he,he,NLS.Poisson.hminusGardnerBracket_comp_meanZeroProjection]
  · exact D.gardner_matrix_complex_meanZero q.val hq q.property σ τ n m
  · exact q.property
  · exact (hillRoughSignedAbelianComponent_analytic D.signed D.signed_analytic σ n
      q.val (D.canonicalDomain_subset_domain hq)).differentiableAt
  · exact (hillRoughSignedAbelianComponent_analytic D.signed D.signed_analytic τ m
      q.val (D.canonicalDomain_subset_domain hq)).differentiableAt

/-- Every raw native restriction is a diffeomorphism of this SAME mean-zero map. -/
theorem exists_originalMeanZeroMap_native_diffeomorphism
    (D : GlobalRoughAbelianForwardData) (s : ℝ) (hs : -1 ≤ s) :
    ∃ e : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev s) ≃ₜ
        physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (s+1/2)),
      AnalyticOnNhd ℝ (fun q => e q) univ ∧ AnalyticOnNhd ℝ e.symm univ ∧
      (∀ q, physicalRealMeanZeroSobolevToComplex hs q ∈ D.originalMeanZeroDomain) ∧
      ∀ q, D.originalMeanZeroMap (physicalRealMeanZeroSobolevToComplex hs q) =
        physicalRealMeanZeroSobolevToComplex (by linarith : (-1/2 : ℝ) ≤ s+1/2) (e q) := by
  obtain ⟨e,hea,heia,hrec⟩ := D.exists_global_raw_real_analytic_sobolev_diffeomorphism s hs
  have hmem (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev s)) :
      physicalRealMeanZeroSobolevToComplex hs q ∈ D.originalMeanZeroDomain := by
    apply D.real_meanZero_mem_canonicalDomain
    · intro j
      simpa only [physicalRealMeanZeroSobolevToComplex_val,WeightedCoeff.sobolevInclusion_apply] using! q.property.1 j
    · simpa only [physicalRealMeanZeroSobolevToComplex_val,WeightedCoeff.sobolevInclusion_apply] using! q.property.2
  refine ⟨e,hea,heia,hmem,?_⟩
  intro q
  apply Subtype.ext
  rw [D.originalMeanZeroMap_val _ (hmem q)]
  exact (hrec q).symm

/-- The actual complex differential of the mean-zero map has exactly the
printed Fourier coefficient, including the inherited source/target norms. -/
theorem originalMeanZeroMap_fourier_differential (D : GlobalRoughAbelianForwardData)
    (h : OriginalComplexBirkhoffSource) (j : ℤ) :
    (((fderiv ℂ D.originalMeanZeroMap 0) h).val).val j =
      (Real.sqrt (2*(j.natAbs : ℝ)*Real.pi) : ℂ)⁻¹*h.val.val j := by
  let P := complexMeanZeroWeightedProjection (Weight.sobolev (-1/2))
  let J := (complexMeanZeroWeightedSubmodule (Weight.sobolev (-1))).subtypeL
  have hd := (D.signed_analytic 0 (D.real_mem_domain 0 (by intro k; simp))).differentiableAt.hasFDerivAt
  have hdJ : HasFDerivAt D.signed (fderiv ℂ D.signed 0) (J 0) := by simpa only [map_zero] using! hd
  have he : fderiv ℂ D.originalMeanZeroMap 0 = P.comp ((fderiv ℂ D.signed 0).comp J) := by
    simpa only [originalMeanZeroMap,Function.comp_def] using!
      (P.hasFDerivAt.comp 0 (hdJ.comp 0 J.hasFDerivAt)).fderiv
  rw [he]
  change (P ((fderiv ℂ D.signed 0) h.val)).val.val j = _
  by_cases hj : j = 0
  · subst j
    rw [show (P ((fderiv ℂ D.signed 0) h.val)).val.val 0 = 0 from (P _).property]
    rw [show h.val.val 0 = 0 from h.property,mul_zero]
  · rw [complexMeanZeroWeightedProjection_apply_other _ _ j hj,
      D.signed_fourier_differential h.val h.property j]

end GlobalRoughAbelianForwardData
end NLS.Articles.KdVKdV2Frequencies
