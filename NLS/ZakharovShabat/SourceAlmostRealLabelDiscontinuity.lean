import NLS.ZakharovShabat.SourcePeriodicLabelDiscontinuity
import NLS.ZakharovShabat.SourceLemma10_2

/-!
# Discontinuous periodic labels on the almost-real source domain

The lexicographic discontinuities persist after restricting to any original-source
neighborhood of zero, including the common domain of Lemma 10.2. The symmetric
coordinates and ordinary simple roots retain all existing analytic properties.
-/

noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Both endpoint labels have a discontinuity within any neighborhood of zero.
The witness lies in its interior, so restricting the source does not remove it. -/
theorem exists_sourcePeriodicLabels_not_continuousWithinAt (hp : p ≠ ⊤) (hp1 : 1 < p)
    (V : Set (CoeffPair p)) (hV : V ∈ 𝓝 (0 : CoeffPair p)) :
    ∃ r : ℝ, 0 < r ∧ sourceConstantPotential (p := p) (r : ℂ) (-r) ∈ interior V ∧
      ¬ContinuousWithinAt (fun ψ : CoeffPair p =>
        canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) 0)
        V (sourceConstantPotential (p := p) (r : ℂ) (-r)) ∧
      ¬ContinuousWithinAt (fun ψ : CoeffPair p =>
        canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) 0)
        V (sourceConstantPotential (p := p) (r : ℂ) (-r)) := by
  obtain ⟨r,hr,hrV,hL,hR⟩ := exists_sourcePeriodicLabels_not_continuousAt
    hp hp1 (interior V) (interior_mem_nhds.mpr hV)
  have hVr : V ∈ 𝓝 (sourceConstantPotential (p := p) (r : ℂ) (-r)) :=
    mem_interior_iff_mem_nhds.mp hrV
  exact ⟨r,hr,hrV,fun h => hL (h.continuousAt hVr),fun h => hR (h.continuousAt hVr)⟩

/-- No neighborhood of zero makes either individually ordered central label continuous. -/
theorem sourcePeriodicLabels_not_continuousOn (hp : p ≠ ⊤) (hp1 : 1 < p)
    (V : Set (CoeffPair p)) (hV : V ∈ 𝓝 (0 : CoeffPair p)) :
    ¬ContinuousOn (fun ψ : CoeffPair p =>
      canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) 0) V ∧
    ¬ContinuousOn (fun ψ : CoeffPair p =>
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) 0) V := by
  obtain ⟨r,_,hrV,hL,hR⟩ := exists_sourcePeriodicLabels_not_continuousWithinAt hp hp1 V hV
  exact ⟨fun h => hL (h _ (interior_subset hrV)),fun h => hR (h _ (interior_subset hrV))⟩

/-- The same Lemma 10.2 domain has analytic symmetric coordinates and discontinuous
individual periodic labels. All isolation, simplicity, and sequence estimates are retained. -/
theorem sourceLemma10_2_with_discontinuous_labels (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ IsConnected W ∧ realTypeSourceLocus p ⊆ W ∧
      SourceLemma10_2Data hp hp1 W ∧
      ¬ContinuousOn (fun ψ : CoeffPair p =>
        canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) 0) W ∧
      ¬ContinuousOn (fun ψ : CoeffPair p =>
        canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) 0) W := by
  obtain ⟨W,hW,hWconn,hreal,hdata⟩ := sourceLemma10_2 hp hp1
  have hzero : (0 : CoeffPair p) ∈ realTypeSourceLocus p := by simp [realTypeSourceLocus]
  exact ⟨W,hW,hWconn,hreal,hdata,sourcePeriodicLabels_not_continuousOn
    hp hp1 W (hW.mem_nhds (hreal hzero))⟩

end NLS.ZakharovShabat
