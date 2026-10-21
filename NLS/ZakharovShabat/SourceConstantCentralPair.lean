import NLS.ZakharovShabat.SourceConstantPeriodicSpectrum
import NLS.ZakharovShabat.SourceIsolatingSpectrum
import NLS.ZakharovShabat.CanonicalPeriodicFree

noncomputable section
open Set Metric
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Near zero, two distinct small constant-potential roots are exactly the canonical central pair. -/
theorem exists_sourceConstant_central_pair_neighborhood (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ U : Set (CoeffPair p), IsOpen U ∧ 0 ∈ U ∧
      ∀ a b z : ℂ, a ≠ 0 → z ≠ 0 → z^2 = a*b →
        sourceConstantPotential a b ∈ U → ‖z‖ < ε →
        canonicalPeriodicLeft hp hp1 (periodOnePotential (sourceConstantPotential a b))
          (periodOnePotential_mem _) 0 = orderedEndpointLeft z (-z) ∧
        canonicalPeriodicRight hp hp1 (periodOnePotential (sourceConstantPotential a b))
          (periodOnePotential_mem _) 0 = orderedEndpointRight z (-z) := by
  obtain ⟨N,ε,hε,_,U,hU,h0,hcluster,hdisjoint⟩ :=
    exists_local_source_pairwise_disjoint_isolating_discs hp hp1 (0 : CoeffPair p)
      (by simpa only [map_zero] using (isRealType_zero (p := p)))
  refine ⟨ε,hε,U,hU,h0,?_⟩
  intro a b z ha hz0 hzsq hψ hz
  have hd : sourceIsolatingDisc hp hp1 (0 : CoeffPair p) N ε 0 = ball 0 ε := by
    simp only [sourceIsolatingDisc, Int.natAbs_zero, Nat.zero_le, if_pos]
    unfold sourceClusterDisc
    simp only [map_zero, canonicalPeriodicLeft_zero, canonicalPeriodicRight_zero]
    norm_num
  have hpos : z ∈ periodicSpectrum hp (periodOnePotential (sourceConstantPotential a b)) :=
    (mem_periodicSpectrum_sourceConstant_iff hp a b z ha).mpr ⟨0,by simpa using hzsq⟩
  have hneg : -z ∈ periodicSpectrum hp (periodOnePotential (sourceConstantPotential a b)) :=
    (mem_periodicSpectrum_sourceConstant_iff hp a b (-z) ha).mpr ⟨0,by simpa using hzsq⟩
  have hposlabel := (source_periodicSpectrum_in_isolatingDisc_iff hp hp1
    (0 : CoeffPair p) (sourceConstantPotential a b) N ε (hcluster _ hψ) hdisjoint 0
    (show z ∈ sourceIsolatingDisc hp hp1 (0 : CoeffPair p) N ε 0 by
      rw [hd]; simpa only [mem_ball, dist_zero_right] using hz)).mp hpos
  have hneglabel := (source_periodicSpectrum_in_isolatingDisc_iff hp hp1
    (0 : CoeffPair p) (sourceConstantPotential a b) N ε (hcluster _ hψ) hdisjoint 0
    (show -z ∈ sourceIsolatingDisc hp hp1 (0 : CoeffPair p) N ε 0 by
      rw [hd]; simpa only [mem_ball, dist_zero_right, norm_neg] using hz)).mp hneg
  let L := canonicalPeriodicLeft hp hp1 (periodOnePotential (sourceConstantPotential a b))
    (periodOnePotential_mem _) 0
  let R := canonicalPeriodicRight hp hp1 (periodOnePotential (sourceConstantPotential a b))
    (periodOnePotential_mem _) 0
  have hne : z ≠ -z := by
    intro he
    apply hz0
    linear_combination (1/2:ℂ)*he
  have hm : ({L,R} : Multiset ℂ) = {z,-z} := by
    rcases hposlabel with hL | hR <;> rcases hneglabel with hnL | hnR
    · exact (hne (hL.trans hnL.symm)).elim
    · rw [show L = z from hL.symm, show R = -z from hnR.symm]
    · rw [show L = -z from hnL.symm, show R = z from hR.symm]
      exact Multiset.pair_comm _ _
    · exact (hne (hR.trans hnR.symm)).elim
  exact NLS.ordered_pair_unique complexLexLE L R
    (orderedEndpointLeft z (-z)) (orderedEndpointRight z (-z))
    (hm.trans (orderedEndpointPair_multiset z (-z)).symm)
    ((canonicalPeriodicEndpoints_spec hp hp1
      (periodOnePotential (sourceConstantPotential a b)) (periodOnePotential_mem _)).2.1 0)
    (orderedEndpointPair_le z (-z))

end NLS.ZakharovShabat
