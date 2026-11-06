import NLS.Articles.MKdVBelowL2.OrdinaryScalarClassicalAdapter
import NLS.Articles.MKdVBelowL2.PhysicalScalarL2Locus
import NLS.Articles.MKdVBelowL2.FixedTimeScalarLocalMassObstruction

/-! # Original mKdV has no continuous fixed-time extension outside L²

The actual ordinary smooth physical map exists and is unique by the PDE.
Its fixed Birkhoff coordinates have the independently calibrated restored
mass phase. A hypothetical extension continuous at a non-L² datum, even
with smooth agreement only in a neighborhood, contradicts the two exact
mass-phase approximation limits at that same selected positive time.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology Complex
open scoped ENNReal
namespace NLS.Articles.MKdVBelowL2
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The fixed-time nonextension clause of Theorem 1.1, equivalently
Corollary 7.2(iii), for every original real datum outside actual physical L².
Agreement with the canonical ordinary smooth map is needed only locally. -/
theorem theorem1_1_fixed_time_nonextension_within (hp : p ≠ ⊤) (h2p : 2 < p)
    (S : PhysicalScalarRealInput p → ℝ → PhysicalScalarRealInput p)
    (hS : IsClassicalOrdinaryScalarSolutionMap S) (u : PhysicalScalarRealInput p)
    (hu : u ∉ physicalScalarL2Locus p) (time : ℝ) (ht : 0 < time)
    (E : PhysicalScalarRealInput p → PhysicalScalarRealInput p)
    (U : Set (PhysicalScalarRealInput p)) (hU : U ∈ 𝓝 u)
    (V : Set (PhysicalScalarRealInput p))
    (hV : ∀ v ∈ U, IsSmoothPhysicalScalarInput v → v ∈ V)
    (hE : ∀ v ∈ U, IsSmoothPhysicalScalarInput v → E v = S v time) : ¬ ContinuousWithinAt E V u := by
  intro hcont
  let hp1 : 1 < p := lt_trans (by norm_num) h2p
  have hnot : ¬ physicalPairHasHilbertRepresentative (physicalScalarPairCLM u) :=
    fun h => hu (mem_physicalScalarL2Locus_of_pair_hilbert u h)
  obtain ⟨n,hn,hmode⟩ := exists_nonzero_physical_birkhoff_index hp hp1 (physicalScalarPairCLM u) hnot
  let G : PhysicalScalarRealInput p → ℂ := fun v =>
    (compatibleBirkhoff hp hp1 (physicalScalarPairCLM (E v)).val).1 n
  have hB : ContinuousAt (compatibleBirkhoff hp hp1) (physicalScalarPairCLM (E u)).val :=
    ((compatibleBirkhoff_analytic hp hp1) _
      ((compatibleBirkhoffDomain_open_real hp hp1).2 (physicalScalarPairCLM (E u)))).continuousAt
  have hpair : ContinuousWithinAt (fun v => (physicalScalarPairCLM (E v)).val) V u :=
    continuous_subtype_val.continuousAt.comp_continuousWithinAt
      (physicalScalarPairCLM.continuous.continuousAt.comp_continuousWithinAt hcont)
  have hG : ContinuousWithinAt G V u :=
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).continuous.continuousAt.comp_continuousWithinAt
      (hB.comp_continuousWithinAt (f := fun v : PhysicalScalarRealInput p => (physicalScalarPairCLM (E v)).val) hpair).fst
  have hc : (-6*(n:ℝ)*time) ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast hn)) ht.ne'
  apply not_continuousWithinAt_fixed_scalar_mass_phase_extension_of_mem_nhds hp h2p.le u hnot
    (-6*(n:ℝ)*time) hc (fourthScalarRenormalizedCoordinate hp hp1 n time)
    (continuous_fourthScalarRenormalizedCoordinate hp hp1 n time).continuousAt
    (fourthScalarRenormalizedCoordinate_ne_zero hp hp1 n time u hmode) G U hU V hV ?_ hG
  intro a ha hs hmem
  change (compatibleBirkhoff hp hp1 (physicalScalarPairCLM (E (fourthClassicalScalarInput h2p.le a ha))).val).1 n = _
  rw [hE _ hmem hs,classicalOrdinaryScalarSolutionMap_coordinates hp hp1 h2p.le S hS a ha hs time n]
  unfold fourthScalarOrdinaryCoordinate
  congr 3
  push_cast
  ring

/-- No continuous ambient fixed-time extension can agree locally with the
canonical ordinary smooth physical solution map. -/
theorem theorem1_1_fixed_time_nonextension (hp : p ≠ ⊤) (h2p : 2 < p)
    (S : PhysicalScalarRealInput p → ℝ → PhysicalScalarRealInput p)
    (hS : IsClassicalOrdinaryScalarSolutionMap S) (u : PhysicalScalarRealInput p)
    (hu : u ∉ physicalScalarL2Locus p) (time : ℝ) (ht : 0 < time)
    (E : PhysicalScalarRealInput p → PhysicalScalarRealInput p)
    (U : Set (PhysicalScalarRealInput p)) (hU : U ∈ 𝓝 u)
    (hE : ∀ v ∈ U, IsSmoothPhysicalScalarInput v → E v = S v time) : ¬ ContinuousAt E u := by
  simpa only [continuousWithinAt_univ] using theorem1_1_fixed_time_nonextension_within
    hp h2p S hS u hu time ht E U hU univ (fun _ _ _ => mem_univ _) hE

/-- Even adjoining one non-L² datum to the smooth data cannot give a
continuous fixed-time extension there, for any selected t>0. -/
theorem theorem1_1_fixed_time_no_smooth_extension (hp : p ≠ ⊤) (h2p : 2 < p)
    (S : PhysicalScalarRealInput p → ℝ → PhysicalScalarRealInput p)
    (hS : IsClassicalOrdinaryScalarSolutionMap S) (u : PhysicalScalarRealInput p)
    (hu : u ∉ physicalScalarL2Locus p) (time : ℝ) (ht : 0 < time)
    (E : PhysicalScalarRealInput p → PhysicalScalarRealInput p)
    (hE : ∀ v : PhysicalScalarRealInput p, IsSmoothPhysicalScalarInput v → E v = S v time) :
    ¬ ContinuousWithinAt E ({v | IsSmoothPhysicalScalarInput v} ∪ {u}) u := by
  exact theorem1_1_fixed_time_nonextension_within hp h2p S hS u hu time ht E univ (Filter.univ_mem)
    ({v | IsSmoothPhysicalScalarInput v} ∪ {u}) (fun _ _ hs => Or.inl hs) (fun v _ hs => hE v hs)

end NLS.Articles.MKdVBelowL2
