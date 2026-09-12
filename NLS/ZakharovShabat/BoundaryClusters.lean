import NLS.ZakharovShabat.BoundaryRootSpaces
import NLS.ZakharovShabat.ContourAnalytic

/-!
# Boundary spectral clusters

Finite sums of the actual boundary root spaces are the boundary intersections
of periodic spectral clusters. Their bounded projections have rank equal to
the sum of boundary algebraic multiplicities, including Jordan chains.
Commutation with the boundary projection identifies the same spaces in the
periodic ambient space and in contour-integral ranges.
-/

open scoped ENNReal
noncomputable section
namespace NLS.ZakharovShabat.BoundaryCondition
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] (b : BoundaryCondition)

theorem projection_idempotent : IsIdempotentElem (projection (p := p) b) := by
  apply ContinuousLinearMap.ext
  intro x
  exact projection_eq_self b (projection_mem b x)

/-- A boundary projection commutes with every individual periodic spectral projection. -/
theorem projection_commute_spectralProjection (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (z : ℂ) :
    Commute (projection b) (periodicSpectralProjection hp φ z) := by
  obtain ⟨w, hw⟩ := ZakharovShabat.resolventSet_nonempty hp φ
  exact commute_periodicSpectralProjection_of_resolvent hp φ w z hw _
    (projection_commute_fullResolvent b hp φ hφ w hw)

theorem projection_commute_clusterProjection (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (s : Finset ℂ) :
    Commute (projection b) (periodicClusterProjection hp φ s) := by
  classical
  exact Commute.sum_right s _ _ fun z _ => projection_commute_spectralProjection b hp φ hφ z

/-- Spectral cluster projection preserves the selected boundary space. -/
theorem periodicClusterProjection_mem (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (s : Finset ℂ) (x : PairSpace p) (hx : x ∈ space b) :
    periodicClusterProjection hp φ s x ∈ space b := by
  have hc := DFunLike.congr_fun (projection_commute_clusterProjection b hp φ hφ s).eq x
  change projection b (periodicClusterProjection hp φ s x) =
    periodicClusterProjection hp φ s (projection b x) at hc
  rw [projection_eq_self b hx] at hc
  rw [← hc]
  exact projection_mem b _

theorem projection_mem_periodicClusterSpace (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (s : Finset ℂ) (x : PairSpace p)
    (hx : x ∈ periodicClusterSpace hp φ s) : projection b x ∈ periodicClusterSpace hp φ s := by
  rw [← range_periodicClusterProjection] at hx ⊢
  obtain ⟨y, rfl⟩ := hx
  exact ⟨projection b y, (DFunLike.congr_fun
    (projection_commute_clusterProjection b hp φ hφ s).eq y).symm⟩

/-- The image of an invariant subspace under the boundary projection is its boundary part. -/
theorem map_projection_eq_inf (M : Submodule ℂ (PairSpace p))
    (hM : ∀ x ∈ M, projection b x ∈ M) : M.map (projection b).toLinearMap = M ⊓ space b := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hM y hy, projection_mem b y⟩
  · rintro ⟨hx, hb⟩
    exact ⟨x, hx, projection_eq_self b hb⟩

/-- A finite cluster of full root spaces inside the actual boundary base space. -/
def clusterSpace (hp : p ≠ ⊤) (φ : PairSpace p) (hφ : φ ∈ dirichletSubspace) (s : Finset ℂ) :
    Submodule ℂ ↥(space (p := p) b) := ⨆ z ∈ s, rootSpaceTop b hp φ hφ z

@[simp] theorem clusterSpace_empty (hp : p ≠ ⊤) (φ : PairSpace p) (hφ : φ ∈ dirichletSubspace) :
    clusterSpace b hp φ hφ ∅ = ⊥ := by simp [clusterSpace]

@[simp] theorem clusterSpace_insert (hp : p ≠ ⊤) (φ : PairSpace p) (hφ : φ ∈ dirichletSubspace)
    (s : Finset ℂ) (z : ℂ) : clusterSpace b hp φ hφ (insert z s) =
      rootSpaceTop b hp φ hφ z ⊔ clusterSpace b hp φ hφ s := by
  classical
  exact Finset.iSup_insert _ _ _

/-- Taking a finite spectral cluster commutes with passage to the boundary restriction. -/
theorem map_clusterSpace (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (s : Finset ℂ) :
    (clusterSpace b hp φ hφ s).map (space b).subtype = periodicClusterSpace hp φ s ⊓ space b := by
  have hr (z : ℂ) : (periodicRootSpaceTop hp φ z).map (projection b).toLinearMap =
      periodicRootSpaceTop hp φ z ⊓ space b :=
    map_projection_eq_inf b _ (projection_mem_periodicRootSpaceTop b hp φ hφ z)
  calc
    _ = (periodicClusterSpace hp φ s).map (projection b).toLinearMap := by
      simp only [clusterSpace, periodicClusterSpace, Submodule.map_iSup, map_rootSpaceTop, hr]
    _ = _ := map_projection_eq_inf b _ (projection_mem_periodicClusterSpace b hp φ hφ s)

theorem mem_clusterSpace_iff_periodic (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (s : Finset ℂ) (x : space (p := p) b) :
    x ∈ clusterSpace b hp φ hφ s ↔ x.val ∈ periodicClusterSpace hp φ s := by
  constructor
  · intro hx
    have hm : x.val ∈ (clusterSpace b hp φ hφ s).map (space b).subtype := ⟨x, hx, rfl⟩
    rw [map_clusterSpace] at hm
    exact hm.1
  · intro hx
    have hm : x.val ∈ (clusterSpace b hp φ hφ s).map (space b).subtype := by
      rw [map_clusterSpace]
      exact ⟨hx, x.property⟩
    obtain ⟨y, hy, he⟩ := hm
    exact (show y = x from Subtype.ext he) ▸ hy

theorem finiteDimensional_clusterSpace (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (s : Finset ℂ) :
    FiniteDimensional ℂ (clusterSpace b hp φ hφ s) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [clusterSpace_empty]; infer_instance
  | @insert z s hz ih =>
    let : FiniteDimensional ℂ (rootSpaceTop b hp φ hφ z) := finiteDimensional_rootSpaceTop b hp φ hφ z
    let : FiniteDimensional ℂ (clusterSpace b hp φ hφ s) := ih
    rw [clusterSpace_insert]
    infer_instance

theorem disjoint_rootSpaceTop_clusterSpace (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (s : Finset ℂ) (z : ℂ) (hz : z ∉ s) :
    Disjoint (rootSpaceTop b hp φ hφ z) (clusterSpace b hp φ hφ s) := by
  apply Submodule.disjoint_def.mpr
  intro x hx hs
  apply Subtype.ext
  exact Submodule.disjoint_def.mp (disjoint_periodicRootSpaceTop_clusterSpace hp φ s z hz) x.val
    ((mem_rootSpaceTop_iff_periodic b hp φ hφ z x).mp hx)
    ((mem_clusterSpace_iff_periodic b hp φ hφ s x).mp hs)

/-- Boundary cluster dimension counts the actual boundary algebraic multiplicities. -/
theorem finrank_clusterSpace (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (s : Finset ℂ) :
    Module.finrank ℂ (clusterSpace b hp φ hφ s) = ∑ z ∈ s, algebraicMultiplicity b hp φ hφ z := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [clusterSpace_empty, finrank_bot, Finset.sum_empty]
  | @insert z s hz ih =>
    let : FiniteDimensional ℂ (rootSpaceTop b hp φ hφ z) := finiteDimensional_rootSpaceTop b hp φ hφ z
    let : FiniteDimensional ℂ (clusterSpace b hp φ hφ s) := finiteDimensional_clusterSpace b hp φ hφ s
    have hd := Submodule.finrank_sup_add_finrank_inf_eq
      (rootSpaceTop b hp φ hφ z) (clusterSpace b hp φ hφ s)
    rw [(disjoint_rootSpaceTop_clusterSpace b hp φ hφ s z hz).eq_bot, finrank_bot, add_zero, ih] at hd
    rw [clusterSpace_insert, Finset.sum_insert hz]
    exact hd

theorem finrank_periodicClusterSpace_inf (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (s : Finset ℂ) :
    Module.finrank ℂ ↥(periodicClusterSpace hp φ s ⊓ space b) =
      ∑ z ∈ s, algebraicMultiplicity b hp φ hφ z := by
  rw [← map_clusterSpace b hp φ hφ s, Submodule.finrank_map_subtype_eq, finrank_clusterSpace]

/-- The boundary component of a cluster projection, acting on the periodic ambient space. -/
def ambientClusterProjection (hp : p ≠ ⊤) (φ : PairSpace p) (s : Finset ℂ) :
    PairSpace p →L[ℂ] PairSpace p := projection b * periodicClusterProjection hp φ s

theorem ambientClusterProjection_idempotent (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (s : Finset ℂ) :
    IsIdempotentElem (ambientClusterProjection b hp φ s) :=
  IsIdempotentElem.mul_of_commute (projection_commute_clusterProjection b hp φ hφ s)
    (projection_idempotent b) (periodicClusterProjection_idempotent hp φ s)

theorem range_ambientClusterProjection (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (s : Finset ℂ) :
    (ambientClusterProjection b hp φ s).range = periodicClusterSpace hp φ s ⊓ space b := by
  have he : (ambientClusterProjection b hp φ s).range =
      (periodicClusterProjection hp φ s).range.map (projection b).toLinearMap :=
    LinearMap.range_comp _ _
  rw [he, range_periodicClusterProjection]
  exact map_projection_eq_inf b _ (projection_mem_periodicClusterSpace b hp φ hφ s)

theorem finrank_range_ambientClusterProjection (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (s : Finset ℂ) :
    Module.finrank ℂ (ambientClusterProjection b hp φ s).range =
      ∑ z ∈ s, algebraicMultiplicity b hp φ hφ z := by
  rw [range_ambientClusterProjection b hp φ hφ s, finrank_periodicClusterSpace_inf]

/-- The ambient boundary component has finite rank for every potential. -/
theorem finiteDimensional_range_ambientClusterProjection (hp : p ≠ ⊤) (φ : PairSpace p)
    (s : Finset ℂ) : FiniteDimensional ℂ (ambientClusterProjection b hp φ s).range := by
  let : FiniteDimensional ℂ (periodicClusterProjection hp φ s).range := by
    rw [range_periodicClusterProjection]
    exact finiteDimensional_periodicClusterSpace hp φ s
  have he : (ambientClusterProjection b hp φ s).range =
      (periodicClusterProjection hp φ s).range.map (projection b).toLinearMap :=
    LinearMap.range_comp _ _
  rw [he]
  infer_instance

theorem isCompactOperator_ambientClusterProjection (hp : p ≠ ⊤) (φ : PairSpace p)
    (s : Finset ℂ) : IsCompactOperator (ambientClusterProjection b hp φ s) :=
  (isCompactOperator_periodicClusterProjection hp φ s).clm_comp (projection b)

/-- The bounded cluster operator on the boundary base space itself. -/
def clusterProjection (hp : p ≠ ⊤) (φ : PairSpace p) (s : Finset ℂ) :
    space (p := p) b →L[ℂ] space (p := p) b :=
  (retract b).comp ((periodicClusterProjection hp φ s).comp (space b).subtypeL)

theorem clusterProjection_val (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (s : Finset ℂ) (x : space (p := p) b) :
    (clusterProjection b hp φ s x).val = periodicClusterProjection hp φ s x.val :=
  projection_eq_self b (periodicClusterProjection_mem b hp φ hφ s x.val x.property)

theorem range_clusterProjection (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (s : Finset ℂ) :
    (clusterProjection b hp φ s).range = clusterSpace b hp φ hφ s := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    rw [mem_clusterSpace_iff_periodic]
    change (clusterProjection b hp φ s y).val ∈ periodicClusterSpace hp φ s
    rw [clusterProjection_val b hp φ hφ, ← range_periodicClusterProjection]
    exact ⟨y.val, rfl⟩
  · intro hx
    rw [mem_clusterSpace_iff_periodic, ← range_periodicClusterProjection] at hx
    obtain ⟨y, hy⟩ := hx
    refine ⟨x, Subtype.ext ?_⟩
    change (clusterProjection b hp φ s x).val = x.val
    rw [clusterProjection_val b hp φ hφ]
    have hid := DFunLike.congr_fun (periodicClusterProjection_idempotent hp φ s).eq y
    change periodicClusterProjection hp φ s (periodicClusterProjection hp φ s y) =
      periodicClusterProjection hp φ s y at hid
    change periodicClusterProjection hp φ s y = x.val at hy
    rwa [hy] at hid

theorem clusterProjection_idempotent (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (s : Finset ℂ) :
    IsIdempotentElem (clusterProjection b hp φ s) := by
  apply ContinuousLinearMap.ext
  intro x
  apply Subtype.ext
  change (clusterProjection b hp φ s (clusterProjection b hp φ s x)).val =
    (clusterProjection b hp φ s x).val
  simp only [clusterProjection_val b hp φ hφ]
  exact DFunLike.congr_fun (periodicClusterProjection_idempotent hp φ s).eq x.val

theorem finrank_range_clusterProjection (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (s : Finset ℂ) :
    Module.finrank ℂ (clusterProjection b hp φ s).range =
      ∑ z ∈ s, algebraicMultiplicity b hp φ hφ z := by
  rw [range_clusterProjection b hp φ hφ s, finrank_clusterSpace]

theorem isTopCompl_clusterSpace_ker_projection (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (s : Finset ℂ) :
    Submodule.IsTopCompl (clusterSpace b hp φ hφ s) (clusterProjection b hp φ s).ker := by
  rw [← range_clusterProjection b hp φ hφ s]
  exact ContinuousLinearMap.IsIdempotentElem.isTopCompl (clusterProjection_idempotent b hp φ hφ s)

/-- The boundary component of a circle projector in the periodic ambient space. -/
def contourProjection (hp : p ≠ ⊤) (φ : PairSpace p) (c : ℂ) (r : ℝ) :
    PairSpace p →L[ℂ] PairSpace p := projection b * resolventCircleIntegral hp φ c r

theorem contourProjection_eq_cluster (hp : p ≠ ⊤) (φ : PairSpace p) (c : ℂ) (r : ℝ)
    (hr : 0 ≤ r) (hc : Metric.sphere c r ⊆ ZakharovShabat.resolventSet hp φ) :
    contourProjection b hp φ c r = ambientClusterProjection b hp φ
      (enclosedPeriodicSpectrum hp φ c r) := by
  unfold contourProjection ambientClusterProjection
  rw [resolventCircleIntegral_eq_clusterProjection hp φ c r hr hc]

theorem contourProjection_idempotent (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : Metric.sphere c r ⊆ ZakharovShabat.resolventSet hp φ) :
    IsIdempotentElem (contourProjection b hp φ c r) := by
  rw [contourProjection_eq_cluster b hp φ c r hr hc]
  exact ambientClusterProjection_idempotent b hp φ hφ _

theorem finiteDimensional_range_contourProjection (hp : p ≠ ⊤) (φ : PairSpace p)
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (hc : Metric.sphere c r ⊆ ZakharovShabat.resolventSet hp φ) :
    FiniteDimensional ℂ (contourProjection b hp φ c r).range := by
  rw [contourProjection_eq_cluster b hp φ c r hr hc]
  exact finiteDimensional_range_ambientClusterProjection b hp φ _

/-- A boundary contour range is exactly the boundary part of the full contour range. -/
theorem range_contourProjection (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : Metric.sphere c r ⊆ ZakharovShabat.resolventSet hp φ) :
    (contourProjection b hp φ c r).range = (resolventCircleIntegral hp φ c r).range ⊓ space b := by
  rw [contourProjection_eq_cluster b hp φ c r hr hc, range_ambientClusterProjection b hp φ hφ,
    range_resolventCircleIntegral hp φ c r hr hc]

/-- The boundary contour rank counts full boundary root spaces, with algebraic multiplicity. -/
theorem finrank_range_contourProjection (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : Metric.sphere c r ⊆ ZakharovShabat.resolventSet hp φ) :
    Module.finrank ℂ (contourProjection b hp φ c r).range =
      ∑ z ∈ enclosedPeriodicSpectrum hp φ c r, algebraicMultiplicity b hp φ hφ z := by
  rw [contourProjection_eq_cluster b hp φ c r hr hc,
    finrank_range_ambientClusterProjection b hp φ hφ]

/-- Boundary contour components inherit operator-norm analyticity on the ambient potential space. -/
theorem analyticAt_contourProjection (hp : p ≠ ⊤) (φ : PairSpace p)
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (hc : Metric.sphere c r ⊆ ZakharovShabat.resolventSet hp φ) :
    AnalyticAt ℂ (fun ψ => contourProjection b hp ψ c r) φ :=
  analyticAt_const.mul (analyticAt_resolventCircleIntegral hp φ c r hr hc)

end NLS.ZakharovShabat.BoundaryCondition
