import NLS.FunctionalAnalysis.CompactTubeBound
import NLS.Dynamics.PhaseAlmostPeriodic
import NLS.SequenceSpaces.PhysicalRealMeanZeroProjection
import NLS.SequenceSpaces.PhysicalRealMeanZeroPhaseFlowExponent

noncomputable section
open Set
open scoped ENNReal
namespace NLS
open WeightedCoeff

/-- One ORIGINAL-norm compact set contains ALL physical phase rotations
of a fixed datum, before every choice of odd frequency and time. -/
theorem exists_compact_physical_weighted_phase_box
    (w : Weight) (hw : ∀ j,w (-j)=w j)
    (z : physicalRealMeanZeroWeightedSubmodule w) :
    ∃ K : Set (physicalRealMeanZeroWeightedSubmodule w),IsCompact K ∧
      ∀ (ω : ℤ → ℝ) (hω : ∀ j,ω (-j)= -ω j) (t : ℝ),
        (physicalRealMeanZeroPhaseFlow w ω hω t z : physicalRealMeanZeroWeightedSubmodule w)∈K := by
  let a := weightIsometry w 2 z.val
  let P := physicalRealMeanZeroProjection w hw
  let H := fun b : Coeff 2 => P ((weightIsometry w 2).symm b)
  let K := H '' {b : Coeff 2 | ∀ n,‖b n‖≤‖a n‖}
  have hH : Continuous H := P.continuous.comp (weightIsometry w 2).symm.continuous
  refine ⟨K,(Coeff.isCompact_dominatedBox (by simp) a).image hH,?_⟩
  intro ω hω t
  refine ⟨Coeff.phaseFlow ω t a,?_,?_⟩
  · intro n
    exact (Coeff.norm_phaseMultiply_apply (fun j => t*ω j) a n).le
  · change P (WeightedCoeff.phaseFlow w ω t z.val)=_
    exact physicalRealMeanZeroProjection_coe w hw
      (physicalRealMeanZeroPhaseFlow w ω hω t z)

end NLS
namespace NLS
open Metric

/-- The bound is uniform for ALL phases and ALL nearby initial targets,
including phases chosen from unrelated data-dependent frequencies. -/
theorem continuous_map_uniformly_bounded_on_nearby_phases
    {F : Type*} [NormedAddCommGroup F]
    (w : Weight) (hw : ∀ j,w (-j)=w j)
    (f : physicalRealMeanZeroWeightedSubmodule w → F) (hf : Continuous f)
    (z : physicalRealMeanZeroWeightedSubmodule w) :
    ∃ δ C : ℝ,0<δ ∧ 0<C ∧
      ∀ z' : physicalRealMeanZeroWeightedSubmodule w,dist z' z<δ →
        ∀ (ω : ℤ → ℝ) (hω : ∀ j,ω (-j)= -ω j) (t : ℝ),
          ‖f (physicalRealMeanZeroPhaseFlow w ω hω t z')‖≤C := by
  obtain ⟨K,hK,hphase⟩ := exists_compact_physical_weighted_phase_box w hw z
  obtain ⟨δ,C,hδ,hC,hbound⟩ := NLS.FunctionalAnalysis.exists_positive_norm_bound_on_compact_tube f hf K hK
  refine ⟨δ,C,hδ,hC,?_⟩
  intro z' hz ω hω t
  apply hbound
  apply Metric.mem_thickening_iff.mpr
  refine ⟨(physicalRealMeanZeroPhaseFlow w ω hω t z : physicalRealMeanZeroWeightedSubmodule w),hphase ω hω t,?_⟩
  have hd : dist (physicalRealMeanZeroPhaseFlow w ω hω t z')
      (physicalRealMeanZeroPhaseFlow w ω hω t z)=dist z' z := by
    change dist (WeightedCoeff.phaseFlow w ω t z'.val) (WeightedCoeff.phaseFlow w ω t z.val)=dist z'.val z.val
    exact (WeightedCoeff.phaseFlow w ω t).isometry.dist_eq z'.val z.val
  exact hd.trans_lt hz

end NLS
