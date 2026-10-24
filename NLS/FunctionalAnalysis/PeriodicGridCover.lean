import NLS.FunctionalAnalysis.PeriodicGridStar
import NLS.FunctionalAnalysis.CoveringDimensionBasic
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Algebra.Order.Archimedean.Basic

/-! # Arbitrarily fine finite covers of a torus with optimal overlap

Periodic grid stars have diameter less than 2/M and multiplicity at most
n+1. The Lebesgue-number lemma therefore produces a refinement of any
finite open cover, proving the standard covering-dimension upper bound.
-/
noncomputable section
set_option autoImplicit false
open Set Metric
namespace NLS.FunctionalAnalysis
universe u
variable {ι : Type u}

/-- Every periodic star contains the image of its vertex. -/
theorem periodicGridStar_center_mem {M : ℕ} (v : ι → Fin M) :
    addCircleGridMap M (fun i => (v i : ℝ)) ∈ periodicGridStar M v := by
  refine ⟨fun i => (v i : ℝ),?_,rfl⟩
  constructor
  · intro i; norm_num
  · intro i j; norm_num

variable [Fintype ι]

/-- Periodic stars have mesh less than twice the reciprocal denominator. -/
theorem dist_lt_of_mem_periodicGridStar {M : ℕ} (hM : 0 < M) {v : ι → Fin M}
    {z w : ι → AddCircle (1 : ℝ)} (hz : z ∈ periodicGridStar M v)
    (hw : w ∈ periodicGridStar M v) : dist z w < 2 / M := by
  obtain ⟨x,hx,rfl⟩ := hz
  obtain ⟨y,hy,rfl⟩ := hw
  apply (dist_pi_lt_iff (by positivity : (0 : ℝ) < 2 / M)).mpr
  intro i
  exact (addCircleGridMap_dist_le hM x y i).trans_lt
    ((div_lt_div_iff_of_pos_right (by positivity : (0 : ℝ) < M)).mpr
      (integerGridStar_coordinate_dist_lt_two hx hy i))

/-- The finite periodic grid cover, indexed in the finite-cover API. -/
def periodicGridCover (M : ℕ) (hM : 0 < M) : FiniteOpenCover (ι → AddCircle (1 : ℝ)) := by
  classical
  exact {
    count := Fintype.card (ι → Fin M)
    sets j := periodicGridStar M ((Fintype.equivFin (ι → Fin M)).symm j)
    isOpen j := isOpen_periodicGridStar hM _
    covers z := by
      obtain ⟨v,hv⟩ := exists_mem_periodicGridStar hM z
      exact ⟨Fintype.equivFin _ v,by simpa only [Equiv.symm_apply_apply] using hv⟩ }

/-- The multiplicity bound survives the finite indexing of the cover. -/
theorem periodicGridCover_multiplicity_le {M : ℕ} (hM : 0 < M)
    (z : ι → AddCircle (1 : ℝ)) :
    (periodicGridCover M hM).multiplicity z ≤ Fintype.card ι + 1 := by
  classical
  let e := (Fintype.equivFin (ι → Fin M)).symm
  let J : Finset (Fin (Fintype.card (ι → Fin M))) :=
    Finset.univ.filter (fun j => z ∈ periodicGridStar M (e j))
  have h := card_le_of_mem_periodicGridStar hM z (fun j : J => e j.val)
    (e.injective.comp Subtype.val_injective)
    (fun j => (Finset.mem_filter.mp j.property).2)
  simpa only [Fintype.card_coe, J, e, periodicGridCover, FiniteOpenCover.multiplicity] using! h

/-- Every finite open cover of the torus admits a sufficiently fine grid refinement. -/
theorem exists_periodicGridCover_refines (U : FiniteOpenCover (ι → AddCircle (1 : ℝ))) :
    ∃ (M : ℕ) (hM : 0 < M), (periodicGridCover M hM).Refines U := by
  classical
  have hc : (Set.univ : Set (ι → AddCircle (1 : ℝ))) ⊆ ⋃ i, U.sets i := by
    intro z _
    obtain ⟨i,hi⟩ := U.covers z
    exact Set.mem_iUnion.mpr ⟨i,hi⟩
  obtain ⟨δ,hδ,hball⟩ := lebesgue_number_lemma_of_metric isCompact_univ U.isOpen hc
  obtain ⟨M,hMd⟩ := exists_nat_gt (2 / δ)
  have hMR : (0 : ℝ) < M := lt_trans (div_pos (by norm_num) hδ) hMd
  have hM : 0 < M := by exact_mod_cast hMR
  have hmesh : (2 : ℝ) / M < δ := by
    apply (div_lt_iff₀ hMR).mpr
    have h := (div_lt_iff₀ hδ).mp hMd
    nlinarith
  refine ⟨M,hM,?_⟩
  intro j
  let v := (Fintype.equivFin (ι → Fin M)).symm j
  let z := addCircleGridMap M (fun i => (v i : ℝ))
  obtain ⟨i,hi⟩ := hball z (Set.mem_univ _)
  refine ⟨i,fun y hy => hi ?_⟩
  exact (dist_lt_of_mem_periodicGridStar hM hy (periodicGridStar_center_mem v)).trans hmesh

/-- A finite product of unit additive circles has covering dimension at most its factor count. -/
theorem hasCoveringDimensionLE_addCircleProduct :
    HasCoveringDimensionLE (ι → AddCircle (1 : ℝ)) (Fintype.card ι) := by
  intro U
  obtain ⟨M,hM,href⟩ := exists_periodicGridCover_refines U
  exact ⟨periodicGridCover M hM,href,periodicGridCover_multiplicity_le hM⟩

end NLS.FunctionalAnalysis
