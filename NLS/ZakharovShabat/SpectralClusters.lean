import NLS.ZakharovShabat.SpectralProjections
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Finite groups of periodic root spaces

Projections at distinct spectral points annihilate each other. Finite sums of
these projections collect root spaces, with rank equal to the sum of their
algebraic multiplicities. These algebraic constructions precede identification
with the contour-integral projectors of Section 3, equation (1.4).
-/

open scoped ENNReal BigOperators
noncomputable section

namespace NLS.ZakharovShabat

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- At a parameter different from the reference point, periodic root spaces are
the generalized eigenspaces of a single resolvent at the reciprocal value. -/
theorem periodicRootSpaceTop_eq_resolvent_genEigenspace (hp : p ≠ ⊤) (φ : PairSpace p)
    (w z : ℂ) (hw : w ∈ resolventSet hp φ) (hzw : z ≠ w) :
    periodicRootSpaceTop hp φ z =
      Module.End.genEigenspace (resolvent hp φ w).toLinearMap (w - z)⁻¹ ⊤ := by
  rw [periodicRootSpaceTop_eq_compact_genEigenspace hp φ w z hw]
  have hc : z - w ≠ 0 := sub_ne_zero.mpr hzw
  apply le_antisymm
  · have h := Module.End.genEigenspace_le_smul
      (((z - w) • resolvent hp φ w).toLinearMap) (-1) (z - w)⁻¹ ⊤
    simpa only [ContinuousLinearMap.toLinearMap_smul, inv_smul_smul₀ hc,
      mul_neg_one, ← inv_neg, neg_sub] using h
  · have h := Module.End.genEigenspace_le_smul
      (resolvent hp φ w).toLinearMap (w - z)⁻¹ (z - w) ⊤
    have heq : (z - w) * (w - z)⁻¹ = -1 := by
      rw [← neg_sub z w, inv_neg, mul_neg, mul_inv_cancel₀ hc]
    simpa only [heq, ContinuousLinearMap.toLinearMap_smul] using h

/-- Full root spaces at distinct parameters have zero intersection. -/
theorem disjoint_periodicRootSpaceTop (hp : p ≠ ⊤) (φ : PairSpace p)
    (z v : ℂ) (hzv : z ≠ v) :
    Disjoint (periodicRootSpaceTop hp φ z) (periodicRootSpaceTop hp φ v) := by
  obtain ⟨w, hw⟩ := resolventSet_nonempty hp φ
  by_cases hzw : z = w
  · subst z
    rw [periodicRootSpaceTop_eq_bot_of_mem_resolventSet hp φ w hw]
    exact disjoint_bot_left
  by_cases hvw : v = w
  · subst v
    rw [periodicRootSpaceTop_eq_bot_of_mem_resolventSet hp φ w hw]
    exact disjoint_bot_right
  rw [periodicRootSpaceTop_eq_resolvent_genEigenspace hp φ w z hw hzw,
    periodicRootSpaceTop_eq_resolvent_genEigenspace hp φ w v hw hvw]
  apply Module.End.disjoint_genEigenspace
  exact fun h => hzv (sub_right_injective (inv_injective h))

/-- A map commuting with a reference resolvent preserves every full root space. -/
theorem mapsTo_periodicRootSpaceTop_of_commute (hp : p ≠ ⊤) (φ : PairSpace p)
    (w z : ℂ) (hw : w ∈ resolventSet hp φ) (A : PairSpace p →L[ℂ] PairSpace p)
    (hA : Commute A (resolvent hp φ w)) :
    Set.MapsTo A (periodicRootSpaceTop hp φ z) (periodicRootSpaceTop hp φ z) := by
  obtain ⟨n, hn⟩ := exists_periodicRootSpace_eq_top hp φ z
  rw [← hn, periodicRootSpace_eq_ker hp φ w z hw]
  have hc : Commute A (boundedRootPencil hp φ w z ^ n) :=
    ((Commute.one_right A).add_right (hA.smul_right (z - w))).pow_right n
  intro x hx
  have hx0 : (boundedRootPencil hp φ w z ^ n) x = 0 := hx
  change (boundedRootPencil hp φ w z ^ n) (A x) = 0
  rw [← show A ((boundedRootPencil hp φ w z ^ n) x) =
    (boundedRootPencil hp φ w z ^ n) (A x) from DFunLike.congr_fun hc.eq x,
    hx0, map_zero]

/-- Spectral projections annihilate root vectors belonging to a different parameter. -/
theorem periodicSpectralProjection_apply_other_root (hp : p ≠ ⊤) (φ : PairSpace p)
    (z v : ℂ) (hzv : z ≠ v) (x : PairSpace p) (hx : x ∈ periodicRootSpaceTop hp φ v) :
    periodicSpectralProjection hp φ z x = 0 := by
  obtain ⟨w, hw⟩ := resolventSet_nonempty hp φ
  apply Submodule.disjoint_def.mp (disjoint_periodicRootSpaceTop hp φ z v hzv)
  · rw [← range_periodicSpectralProjection hp φ z]
    exact LinearMap.mem_range_self _ x
  · exact mapsTo_periodicRootSpaceTop_of_commute hp φ w v hw _
      (periodicSpectralProjection_commute_resolvent hp φ z w hw) hx

/-- Distinct periodic spectral projections annihilate each other. -/
theorem periodicSpectralProjection_mul_eq_zero (hp : p ≠ ⊤) (φ : PairSpace p)
    (z v : ℂ) (hzv : z ≠ v) :
    periodicSpectralProjection hp φ z * periodicSpectralProjection hp φ v = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  apply periodicSpectralProjection_apply_other_root hp φ z v hzv
  rw [← range_periodicSpectralProjection hp φ v]
  exact LinearMap.mem_range_self _ x

/-- All periodic spectral projections commute, including at coincident parameters. -/
theorem periodicSpectralProjection_commute (hp : p ≠ ⊤) (φ : PairSpace p) (z v : ℂ) :
    Commute (periodicSpectralProjection hp φ z) (periodicSpectralProjection hp φ v) := by
  by_cases h : z = v
  · subst v; exact Commute.refl _
  change _ * _ = _ * _
  rw [periodicSpectralProjection_mul_eq_zero hp φ z v h,
    periodicSpectralProjection_mul_eq_zero hp φ v z (Ne.symm h)]

/-- The sum of the root spaces indexed by a finite set of parameters. -/
def periodicClusterSpace (hp : p ≠ ⊤) (φ : PairSpace p) (s : Finset ℂ) :
    Submodule ℂ (PairSpace p) := ⨆ z ∈ s, periodicRootSpaceTop hp φ z

/-- The bounded projection collecting a finite set of periodic root spaces. -/
def periodicClusterProjection (hp : p ≠ ⊤) (φ : PairSpace p) (s : Finset ℂ) :
    PairSpace p →L[ℂ] PairSpace p := ∑ z ∈ s, periodicSpectralProjection hp φ z

@[simp] theorem periodicClusterSpace_empty (hp : p ≠ ⊤) (φ : PairSpace p) :
    periodicClusterSpace hp φ ∅ = ⊥ := by simp [periodicClusterSpace]

@[simp] theorem periodicClusterSpace_insert (hp : p ≠ ⊤) (φ : PairSpace p)
    (s : Finset ℂ) (z : ℂ) :
    periodicClusterSpace hp φ (insert z s) = periodicRootSpaceTop hp φ z ⊔
      periodicClusterSpace hp φ s := by
  classical
  exact Finset.iSup_insert _ _ _

@[simp] theorem periodicClusterProjection_empty (hp : p ≠ ⊤) (φ : PairSpace p) :
    periodicClusterProjection hp φ ∅ = 0 := by simp [periodicClusterProjection]

/-- A finite cluster projection fixes each root vector indexed by that cluster. -/
theorem periodicClusterProjection_apply_root (hp : p ≠ ⊤) (φ : PairSpace p)
    (s : Finset ℂ) (z : ℂ) (hz : z ∈ s) (x : PairSpace p)
    (hx : x ∈ periodicRootSpaceTop hp φ z) : periodicClusterProjection hp φ s x = x := by
  classical
  simp only [periodicClusterProjection, sum_apply]
  rw [Finset.sum_eq_single z]
  · exact periodicSpectralProjection_apply_root hp φ z x hx
  · intro v _ hv
    exact periodicSpectralProjection_apply_other_root hp φ v z hv x hx
  · exact fun h => False.elim (h hz)

/-- Root vectors outside a cluster are annihilated by its projection. -/
theorem periodicClusterProjection_apply_other_root (hp : p ≠ ⊤) (φ : PairSpace p)
    (s : Finset ℂ) (z : ℂ) (hz : z ∉ s) (x : PairSpace p)
    (hx : x ∈ periodicRootSpaceTop hp φ z) : periodicClusterProjection hp φ s x = 0 := by
  classical
  simp only [periodicClusterProjection, sum_apply]
  apply Finset.sum_eq_zero
  intro v hv
  exact periodicSpectralProjection_apply_other_root hp φ v z
    (fun h => hz (h ▸ hv)) x hx

/-- The cluster projection has exactly the finite sum of root spaces as its range. -/
theorem range_periodicClusterProjection (hp : p ≠ ⊤) (φ : PairSpace p) (s : Finset ℂ) :
    (periodicClusterProjection hp φ s).range = periodicClusterSpace hp φ s := by
  classical
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    change periodicClusterProjection hp φ s y ∈ periodicClusterSpace hp φ s
    rw [periodicClusterProjection, sum_apply]
    apply Submodule.sum_mem
    intro z hz
    have hle : periodicRootSpaceTop hp φ z ≤ periodicClusterSpace hp φ s :=
      le_iSup_of_le z (le_iSup_of_le hz le_rfl)
    apply hle
    rw [← range_periodicSpectralProjection hp φ z]
    exact LinearMap.mem_range_self _ y
  · apply iSup_le
    intro z
    apply iSup_le
    intro hz x hx
    exact ⟨x, periodicClusterProjection_apply_root hp φ s z hz x hx⟩

/-- Finite sums of mutually annihilating root projections are idempotent. -/
theorem periodicClusterProjection_idempotent (hp : p ≠ ⊤) (φ : PairSpace p) (s : Finset ℂ) :
    IsIdempotentElem (periodicClusterProjection hp φ s) := by
  classical
  apply ContinuousLinearMap.ext
  intro x
  change periodicClusterProjection hp φ s (periodicClusterProjection hp φ s x) =
    periodicClusterProjection hp φ s x
  rw [show periodicClusterProjection hp φ s x =
    ∑ z ∈ s, periodicSpectralProjection hp φ z x by simp [periodicClusterProjection]]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro z hz
  apply periodicClusterProjection_apply_root hp φ s z hz
  rw [← range_periodicSpectralProjection hp φ z]
  exact LinearMap.mem_range_self _ x

/-- A finite cluster projection commutes with each individual spectral projection. -/
theorem periodicClusterProjection_commute_projection (hp : p ≠ ⊤) (φ : PairSpace p)
    (s : Finset ℂ) (z : ℂ) :
    Commute (periodicClusterProjection hp φ s) (periodicSpectralProjection hp φ z) := by
  classical
  exact Commute.sum_left s _ _ fun v _ => periodicSpectralProjection_commute hp φ v z

/-- The cluster kernel is the intersection of its individual projection kernels. -/
theorem ker_periodicClusterProjection (hp : p ≠ ⊤) (φ : PairSpace p) (s : Finset ℂ) :
    (periodicClusterProjection hp φ s).ker =
      ⨅ z ∈ s, (periodicSpectralProjection hp φ z).ker := by
  classical
  ext x
  simp only [Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro hx z hz
    have hc := DFunLike.congr_fun (periodicClusterProjection_commute_projection hp φ s z).eq x
    change periodicClusterProjection hp φ s (periodicSpectralProjection hp φ z x) =
      periodicSpectralProjection hp φ z (periodicClusterProjection hp φ s x) at hc
    have hmem : periodicSpectralProjection hp φ z x ∈ periodicRootSpaceTop hp φ z := by
      rw [← range_periodicSpectralProjection hp φ z]
      exact LinearMap.mem_range_self _ x
    rw [periodicClusterProjection_apply_root hp φ s z hz _ hmem] at hc
    change periodicClusterProjection hp φ s x = 0 at hx
    rw [hx, map_zero] at hc
    exact hc
  · intro hx
    change periodicClusterProjection hp φ s x = 0
    rw [periodicClusterProjection, sum_apply]
    exact Finset.sum_eq_zero fun z hz => hx z hz

/-- Finite spectral clusters have finite-dimensional root spaces. -/
theorem finiteDimensional_periodicClusterSpace (hp : p ≠ ⊤) (φ : PairSpace p) (s : Finset ℂ) :
    FiniteDimensional ℂ (periodicClusterSpace hp φ s) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have heq : periodicClusterSpace hp φ ∅ = ⊥ := by simp [periodicClusterSpace]
    rw [heq]
    infer_instance
  | @insert z s hz ih =>
    let : FiniteDimensional ℂ (periodicRootSpaceTop hp φ z) :=
      finiteDimensional_periodicRootSpaceTop hp φ z
    let : FiniteDimensional ℂ (periodicClusterSpace hp φ s) := ih
    change FiniteDimensional ℂ (⨆ v ∈ insert z s, periodicRootSpaceTop hp φ v :
      Submodule ℂ (PairSpace p))
    rw [Finset.iSup_insert]
    change FiniteDimensional ℂ (periodicRootSpaceTop hp φ z ⊔ periodicClusterSpace hp φ s :
      Submodule ℂ (PairSpace p))
    infer_instance

/-- A root space outside a finite cluster has zero intersection with the cluster. -/
theorem disjoint_periodicRootSpaceTop_clusterSpace (hp : p ≠ ⊤) (φ : PairSpace p)
    (s : Finset ℂ) (z : ℂ) (hz : z ∉ s) :
    Disjoint (periodicRootSpaceTop hp φ z) (periodicClusterSpace hp φ s) := by
  have hle : periodicClusterSpace hp φ s ≤ (periodicSpectralProjection hp φ z).ker := by
    apply iSup_le
    intro v
    apply iSup_le
    intro hv x hx
    exact periodicSpectralProjection_apply_other_root hp φ z v
      (fun h => hz (h ▸ hv)) x hx
  apply Submodule.disjoint_def.mpr
  intro x hx hs
  have hzero : periodicSpectralProjection hp φ z x = 0 := hle hs
  rwa [periodicSpectralProjection_apply_root hp φ z x hx] at hzero

/-- The dimension of a finite cluster is the sum of its algebraic multiplicities. -/
theorem finrank_periodicClusterSpace (hp : p ≠ ⊤) (φ : PairSpace p) (s : Finset ℂ) :
    Module.finrank ℂ (periodicClusterSpace hp φ s) =
      ∑ z ∈ s, periodicAlgebraicMultiplicity hp φ z := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [periodicClusterSpace_empty, finrank_bot, Finset.sum_empty]
  | @insert z s hz ih =>
    let : FiniteDimensional ℂ (periodicRootSpaceTop hp φ z) :=
      finiteDimensional_periodicRootSpaceTop hp φ z
    let : FiniteDimensional ℂ (periodicClusterSpace hp φ s) :=
      finiteDimensional_periodicClusterSpace hp φ s
    have hd := Submodule.finrank_sup_add_finrank_inf_eq
      (periodicRootSpaceTop hp φ z) (periodicClusterSpace hp φ s)
    rw [(disjoint_periodicRootSpaceTop_clusterSpace hp φ s z hz).eq_bot,
      finrank_bot, add_zero, ih] at hd
    rw [periodicClusterSpace_insert, Finset.sum_insert hz]
    exact hd

/-- The rank of a cluster projection counts algebraic multiplicities in the cluster. -/
theorem finrank_range_periodicClusterProjection (hp : p ≠ ⊤) (φ : PairSpace p) (s : Finset ℂ) :
    Module.finrank ℂ (periodicClusterProjection hp φ s).range =
      ∑ z ∈ s, periodicAlgebraicMultiplicity hp φ z := by
  rw [range_periodicClusterProjection]
  exact finrank_periodicClusterSpace hp φ s

/-- Cluster projections commute with all resolvents. -/
theorem periodicClusterProjection_commute_resolvent (hp : p ≠ ⊤) (φ : PairSpace p)
    (s : Finset ℂ) (w : ℂ) (hw : w ∈ resolventSet hp φ) :
    Commute (periodicClusterProjection hp φ s) (resolvent hp φ w) := by
  classical
  exact Commute.sum_left s _ _ fun z _ => periodicSpectralProjection_commute_resolvent hp φ z w hw

/-- Each cluster and its projection kernel form a topological direct sum. -/
theorem isTopCompl_periodicClusterSpace_ker_projection (hp : p ≠ ⊤)
    (φ : PairSpace p) (s : Finset ℂ) :
    Submodule.IsTopCompl (periodicClusterSpace hp φ s) (periodicClusterProjection hp φ s).ker := by
  rw [← range_periodicClusterProjection hp φ s]
  exact ContinuousLinearMap.IsIdempotentElem.isTopCompl
    (periodicClusterProjection_idempotent hp φ s)

/-- Composing finite cluster projections selects the intersection of their parameters. -/
theorem periodicClusterProjection_mul (hp : p ≠ ⊤) (φ : PairSpace p) (s t : Finset ℂ) :
    periodicClusterProjection hp φ s * periodicClusterProjection hp φ t =
      periodicClusterProjection hp φ (s ∩ t) := by
  classical
  apply ContinuousLinearMap.ext
  intro x
  change periodicClusterProjection hp φ s (periodicClusterProjection hp φ t x) =
    periodicClusterProjection hp φ (s ∩ t) x
  rw [show periodicClusterProjection hp φ t x =
    ∑ z ∈ t, periodicSpectralProjection hp φ z x by simp [periodicClusterProjection], map_sum]
  have hmem (z : ℂ) : periodicSpectralProjection hp φ z x ∈ periodicRootSpaceTop hp φ z := by
    rw [← range_periodicSpectralProjection hp φ z]
    exact LinearMap.mem_range_self _ x
  calc
    _ = ∑ z ∈ s ∩ t, periodicClusterProjection hp φ s (periodicSpectralProjection hp φ z x) := by
      symm
      apply Finset.sum_subset Finset.inter_subset_right
      intro z hzt hz
      apply periodicClusterProjection_apply_other_root hp φ s z _ _ (hmem z)
      exact fun hzs => hz (Finset.mem_inter.mpr ⟨hzs, hzt⟩)
    _ = ∑ z ∈ s ∩ t, periodicSpectralProjection hp φ z x := by
      apply Finset.sum_congr rfl
      intro z hz
      exact periodicClusterProjection_apply_root hp φ s z (Finset.mem_inter.mp hz).1 _ (hmem z)
    _ = _ := by simp [periodicClusterProjection]

/-- Disjoint finite clusters have mutually annihilating projections. -/
theorem periodicClusterProjection_mul_eq_zero (hp : p ≠ ⊤) (φ : PairSpace p)
    (s t : Finset ℂ) (hst : Disjoint s t) :
    periodicClusterProjection hp φ s * periodicClusterProjection hp φ t = 0 := by
  rw [periodicClusterProjection_mul, Finset.disjoint_iff_inter_eq_empty.mp hst,
    periodicClusterProjection_empty]

/-- Finite cluster projections are compact operators. -/
theorem isCompactOperator_periodicClusterProjection (hp : p ≠ ⊤)
    (φ : PairSpace p) (s : Finset ℂ) : IsCompactOperator (periodicClusterProjection hp φ s) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [periodicClusterProjection_empty]; exact isCompactOperator_zero
  | @insert z s hz ih =>
    have heq : periodicClusterProjection hp φ (insert z s) =
        periodicSpectralProjection hp φ z + periodicClusterProjection hp φ s :=
      Finset.sum_insert hz
    rw [heq]
    exact (isCompactOperator_periodicSpectralProjection hp φ z).add ih

/-- Each vector splits uniquely into its finite-cluster part and a complement. -/
theorem existsUnique_periodicCluster_decomposition (hp : p ≠ ⊤) (φ : PairSpace p)
    (s : Finset ℂ) (x : PairSpace p) :
    ∃! uv : periodicClusterSpace hp φ s × (periodicClusterProjection hp φ s).ker,
      (uv.1 : PairSpace p) + uv.2 = x :=
  Submodule.existsUnique_add_of_isCompl_prod
    (isTopCompl_periodicClusterSpace_ker_projection hp φ s).isCompl x

end NLS.ZakharovShabat
