import NLS.ZakharovShabat.RootSpaces
import NLS.ZakharovShabat.ResolventCalculus
import NLS.FunctionalAnalysis.CompactDecomposition

/-!
# Bounded periodic spectral projections

The full root space has a closed complement given by the range of a stabilized
bounded-pencil power. Projection along this complement commutes with every
resolvent and is independent of the reference resolvent parameter.
Identification with contour-integral Riesz projections is a separate result.
-/

open scoped ENNReal
noncomputable section

namespace NLS.ZakharovShabat

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Any stabilized bounded-pencil power gives a topological decomposition. -/
theorem isTopCompl_periodicRootSpaceTop_range (hp : p ≠ ⊤) (φ : PairSpace p)
    (w z : ℂ) (hw : w ∈ resolventSet hp φ) (n : ℕ)
    (hn : periodicRootSpace hp φ z n = periodicRootSpaceTop hp φ z) :
    Submodule.IsTopCompl (periodicRootSpaceTop hp φ z)
      ((boundedRootPencil hp φ w z) ^ n).range := by
  rw [periodicRootSpace_eq_compact_genEigenspace hp φ w z hw,
    periodicRootSpaceTop_eq_compact_genEigenspace hp φ w z hw] at hn
  rw [periodicRootSpaceTop_eq_compact_genEigenspace hp φ w z hw]
  have heq : boundedRootPencil hp φ w z =
      (z - w) • resolvent hp φ w - (-1 : ℂ) • 1 := by
    unfold boundedRootPencil
    module
  rw [heq]
  exact NLS.CompactSpectrum.isTopCompl_genEigenspace_range_pow _
    ((isCompactOperator_resolvent hp φ w).smul (z - w)) (by norm_num) n hn

private def rootIndex (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ) : ℕ :=
  (exists_periodicRootSpace_eq_top hp φ z).choose

private theorem rootIndex_spec (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ) :
    periodicRootSpace hp φ z (rootIndex hp φ z) = periodicRootSpaceTop hp φ z :=
  (exists_periodicRootSpace_eq_top hp φ z).choose_spec

private def rootComplement (hp : p ≠ ⊤) (φ : PairSpace p) (w z : ℂ) :
    Submodule ℂ (PairSpace p) := ((boundedRootPencil hp φ w z) ^ rootIndex hp φ z).range

private theorem rootTopCompl (hp : p ≠ ⊤) (φ : PairSpace p) (w z : ℂ)
    (hw : w ∈ resolventSet hp φ) :
    Submodule.IsTopCompl (periodicRootSpaceTop hp φ z) (rootComplement hp φ w z) :=
  isTopCompl_periodicRootSpaceTop_range hp φ w z hw _ (rootIndex_spec hp φ z)

private def projectionAt (hp : p ≠ ⊤) (φ : PairSpace p) (w z : ℂ)
    (hw : w ∈ resolventSet hp φ) : PairSpace p →L[ℂ] PairSpace p :=
  (periodicRootSpaceTop hp φ z).projectionL (rootComplement hp φ w z)
    (rootTopCompl hp φ w z hw)

private theorem projectionAt_mem (hp : p ≠ ⊤) (φ : PairSpace p) (w z : ℂ)
    (hw : w ∈ resolventSet hp φ) (x : PairSpace p) :
    projectionAt hp φ w z hw x ∈ periodicRootSpaceTop hp φ z :=
  Submodule.projectionL_apply_mem _ x

private theorem projectionAt_apply_root (hp : p ≠ ⊤) (φ : PairSpace p) (w z : ℂ)
    (hw : w ∈ resolventSet hp φ) (x : PairSpace p)
    (hx : x ∈ periodicRootSpaceTop hp φ z) : projectionAt hp φ w z hw x = x :=
  Submodule.projectionL_apply_left _ ⟨x, hx⟩

private theorem commute_projectionAt (hp : p ≠ ⊤) (φ : PairSpace p) (w z : ℂ)
    (hw : w ∈ resolventSet hp φ) (A : PairSpace p →L[ℂ] PairSpace p)
    (hA : Commute A (resolvent hp φ w)) : Commute A (projectionAt hp φ w z hw) := by
  have hB : Commute A ((boundedRootPencil hp φ w z) ^ rootIndex hp φ z) :=
    ((Commute.one_right A).add_right (hA.smul_right (z - w))).pow_right _
  have hker : periodicRootSpaceTop hp φ z =
      ((boundedRootPencil hp φ w z) ^ rootIndex hp φ z).ker := by
    rw [← rootIndex_spec hp φ z, periodicRootSpace_eq_ker hp φ w z hw]
  unfold projectionAt
  generalize rootTopCompl hp φ w z hw = h
  unfold rootComplement at h ⊢
  revert h
  rw [hker]
  intro h
  exact NLS.CompactSpectrum.commute_projectionL_ker_range hB h

private theorem resolvent_commute_projectionAt (hp : p ≠ ⊤) (φ : PairSpace p) (w z v : ℂ)
    (hw : w ∈ resolventSet hp φ) (hv : v ∈ resolventSet hp φ) :
    Commute (resolvent hp φ v) (projectionAt hp φ w z hw) :=
  commute_projectionAt hp φ w z hw _ (resolvent_commute hp φ v w hv hw)

private theorem projectionAt_eq (hp : p ≠ ⊤) (φ : PairSpace p) (w v z : ℂ)
    (hw : w ∈ resolventSet hp φ) (hv : v ∈ resolventSet hp φ) :
    projectionAt hp φ w z hw = projectionAt hp φ v z hv := by
  have hc := commute_projectionAt hp φ v z hv _
    (resolvent_commute_projectionAt hp φ w z v hw hv).symm
  apply ContinuousLinearMap.ext
  intro x
  have hx := DFunLike.congr_fun hc.eq x
  change projectionAt hp φ w z hw (projectionAt hp φ v z hv x) =
    projectionAt hp φ v z hv (projectionAt hp φ w z hw x) at hx
  rw [projectionAt_apply_root hp φ w z hw _ (projectionAt_mem hp φ v z hv x),
    projectionAt_apply_root hp φ v z hv _ (projectionAt_mem hp φ w z hw x)] at hx
  exact hx.symm

/-- The bounded projection onto the full periodic root space along its invariant
complement. Its value is independent of the chosen reference resolvent point. -/
def periodicSpectralProjection (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ) :
    PairSpace p →L[ℂ] PairSpace p :=
  projectionAt hp φ (resolventSet_nonempty hp φ).choose z
    (resolventSet_nonempty hp φ).choose_spec

/-- The projection has exactly the full root space as its range. -/
theorem range_periodicSpectralProjection (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ) :
    (periodicSpectralProjection hp φ z).range = periodicRootSpaceTop hp φ z :=
  Submodule.range_projectionL _

/-- Every root vector is fixed by the spectral projection. -/
theorem periodicSpectralProjection_apply_root (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ)
    (x : PairSpace p) (hx : x ∈ periodicRootSpaceTop hp φ z) :
    periodicSpectralProjection hp φ z x = x :=
  projectionAt_apply_root hp φ _ z _ x hx

/-- The bounded spectral projection is idempotent. -/
theorem periodicSpectralProjection_idempotent (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ) :
    IsIdempotentElem (periodicSpectralProjection hp φ z) :=
  Submodule.isIdempotentElem_projectionL _

/-- The spectral projection commutes with every resolvent. -/
theorem periodicSpectralProjection_commute_resolvent (hp : p ≠ ⊤) (φ : PairSpace p)
    (z w : ℂ) (hw : w ∈ resolventSet hp φ) :
    Commute (periodicSpectralProjection hp φ z) (resolvent hp φ w) :=
  (resolvent_commute_projectionAt hp φ _ z w _ hw).symm

/-- Commutation with one resolvent implies commutation with every root-space projection. -/
theorem commute_periodicSpectralProjection_of_resolvent (hp : p ≠ ⊤) (φ : PairSpace p)
    (w z : ℂ) (hw : w ∈ resolventSet hp φ) (A : PairSpace p →L[ℂ] PairSpace p)
    (hA : Commute A (resolvent hp φ w)) : Commute A (periodicSpectralProjection hp φ z) := by
  unfold periodicSpectralProjection
  rw [projectionAt_eq hp φ _ w z _ hw]
  exact commute_projectionAt hp φ w z hw A hA

/-- The projection has finite rank. -/
theorem finiteDimensional_range_periodicSpectralProjection (hp : p ≠ ⊤)
    (φ : PairSpace p) (z : ℂ) : FiniteDimensional ℂ (periodicSpectralProjection hp φ z).range := by
  rw [range_periodicSpectralProjection]
  exact finiteDimensional_periodicRootSpaceTop hp φ z

/-- Finite rank makes the spectral projection a compact operator. -/
theorem isCompactOperator_periodicSpectralProjection (hp : p ≠ ⊤)
    (φ : PairSpace p) (z : ℂ) : IsCompactOperator (periodicSpectralProjection hp φ z) := by
  let N := periodicRootSpaceTop hp φ z
  let : FiniteDimensional ℂ N := finiteDimensional_periodicRootSpaceTop hp φ z
  let : LocallyCompactSpace N := LocallyCompactSpace.of_finiteDimensional_of_complete ℂ N
  let Q := (periodicSpectralProjection hp φ z).codRestrict N
    (projectionAt_mem hp φ _ z _)
  exact (isCompactOperator_of_locallyCompactSpace_dom Q).clm_comp N.subtypeL

/-- Its rank equals the previously defined algebraic multiplicity. -/
theorem finrank_range_periodicSpectralProjection (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ) :
    Module.finrank ℂ (periodicSpectralProjection hp φ z).range =
      periodicAlgebraicMultiplicity hp φ z := by
  rw [range_periodicSpectralProjection]
  rfl

/-- The same stabilized exponent describes the projection kernel at every
reference resolvent point. -/
theorem exists_ker_periodicSpectralProjection_eq_range (hp : p ≠ ⊤)
    (φ : PairSpace p) (z : ℂ) :
    ∃ n : ℕ, periodicRootSpace hp φ z n = periodicRootSpaceTop hp φ z ∧
      ∀ w ∈ resolventSet hp φ, (periodicSpectralProjection hp φ z).ker =
        ((boundedRootPencil hp φ w z) ^ n).range := by
  refine ⟨rootIndex hp φ z, rootIndex_spec hp φ z, ?_⟩
  intro w hw
  unfold periodicSpectralProjection
  rw [projectionAt_eq hp φ _ w z _ hw]
  exact Submodule.ker_projectionL _

/-- The root space and the projection kernel give a topological direct sum. -/
theorem isTopCompl_periodicRootSpaceTop_ker_projection (hp : p ≠ ⊤)
    (φ : PairSpace p) (z : ℂ) :
    Submodule.IsTopCompl (periodicRootSpaceTop hp φ z)
      (periodicSpectralProjection hp φ z).ker := by
  rw [← range_periodicSpectralProjection hp φ z]
  exact ContinuousLinearMap.IsIdempotentElem.isTopCompl
    (periodicSpectralProjection_idempotent hp φ z)

/-- Every base vector has a unique root-space/complement decomposition. -/
theorem existsUnique_periodicRootSpace_decomposition (hp : p ≠ ⊤)
    (φ : PairSpace p) (z : ℂ) (x : PairSpace p) :
    ∃! uv : periodicRootSpaceTop hp φ z × (periodicSpectralProjection hp φ z).ker,
      (uv.1 : PairSpace p) + uv.2 = x :=
  Submodule.existsUnique_add_of_isCompl_prod
    (isTopCompl_periodicRootSpaceTop_ker_projection hp φ z).isCompl x

/-- Projection vanishes precisely at resolvent points. -/
theorem periodicSpectralProjection_eq_zero_iff (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ) :
    periodicSpectralProjection hp φ z = 0 ↔ z ∈ resolventSet hp φ := by
  constructor
  · intro h
    have hr : periodicRootSpaceTop hp φ z = ⊥ := by
      rw [← range_periodicSpectralProjection hp φ z, h]
      exact LinearMap.range_zero
    by_contra hz
    exact (periodicRootSpaceTop_ne_bot_iff hp φ z).mpr hz hr
  · intro hz
    apply ContinuousLinearMap.ext
    intro x
    have hx := projectionAt_mem hp φ (resolventSet_nonempty hp φ).choose z
      (resolventSet_nonempty hp φ).choose_spec x
    rw [periodicRootSpaceTop_eq_bot_of_mem_resolventSet hp φ z hz] at hx
    exact hx

end NLS.ZakharovShabat
