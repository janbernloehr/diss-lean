import NLS.ZakharovShabat.SourceTriangularCollapsedWitness
import NLS.ZakharovShabat.SourceConstantCentralPair
import NLS.ZakharovShabat.SourceGapWeightedEtaOriginalCollapsed

noncomputable section
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Near zero, every nonzero triangular constant source is the limit of an actual
sequence of open central gaps, inside any prescribed open neighborhood. -/
theorem exists_sourceConstant_open_gap_approach_neighborhood (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ 0 ∈ U ∧
      ∀ a : ℂ, a ≠ 0 → sourceConstantPotential a 0 ∈ U →
      ∀ W : Set (CoeffPair p), IsOpen W → sourceConstantPotential a 0 ∈ W →
      ∃ u : ℕ → CoeffPair p,
        (∀ k, u k ∈ W ∧ canonicalPeriodicGap hp hp1 (periodOnePotential (u k))
          (periodOnePotential_mem _) 0 ≠ 0) ∧
        Tendsto u atTop (𝓝 (sourceConstantPotential a 0)) := by
  obtain ⟨ε,hε,U,hU,h0,hpair⟩ := exists_sourceConstant_central_pair_neighborhood hp hp1
  refine ⟨U,hU,h0,?_⟩
  intro a ha haU W hW haW
  let z : ℕ → ℂ := fun k => 1 / ((k : ℂ)+1)
  let u : ℕ → CoeffPair p := fun k => sourceConstantPotential a ((z k)^2/a)
  have hz : Tendsto z atTop (𝓝 (0 : ℂ)) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hz0 (k : ℕ) : z k ≠ 0 := by
    apply div_ne_zero one_ne_zero
    have hn : (k : ℝ)+1 ≠ 0 := by positivity
    exact_mod_cast hn
  have hb : Tendsto (fun k => (z k)^2/a) atTop (𝓝 (0 : ℂ)) := by
    simpa only [zero_pow (by decide : (2:ℕ) ≠ 0),zero_div] using (hz.pow 2).div_const a
  have hu : Tendsto u atTop (𝓝 (sourceConstantPotential a 0)) := by
    have hparam : Tendsto (fun k : ℕ => (a,(z k)^2/a)) atTop (𝓝 (a,(0 : ℂ))) :=
      tendsto_const_nhds.prodMk_nhds hb
    have hc : ContinuousAt (fun v : ℂ × ℂ => sourceConstantPotential (p := p) v.1 v.2) (a,0) :=
      (continuous_sourceConstantPotential (p := p)).continuousAt
    simpa only [Function.comp_def] using hc.tendsto.comp hparam
  have hnear : ∀ᶠ k in atTop, u k ∈ U ∩ W :=
    hu.eventually ((hU.inter hW).mem_nhds ⟨haU,haW⟩)
  have hsmall : ∀ᶠ k in atTop, ‖z k‖ < ε := by
    exact hz.norm.eventually (by simpa only [norm_zero] using gt_mem_nhds hε)
  have hopen : ∀ᶠ k in atTop, u k ∈ W ∧ canonicalPeriodicGap hp hp1
      (periodOnePotential (u k)) (periodOnePotential_mem _) 0 ≠ 0 := by
    filter_upwards [hnear,hsmall] with k hk hs
    have hlr := hpair a ((z k)^2/a) (z k) ha (hz0 k) (by field_simp) hk.1 hs
    refine ⟨hk.2,?_⟩
    simp only [canonicalPeriodicGap,u,hlr.1,hlr.2,sub_ne_zero]
    unfold orderedEndpointLeft orderedEndpointRight
    split_ifs <;> intro he <;> apply hz0 k
    · linear_combination -he / 2
    · linear_combination he / 2
  obtain ⟨N,hN⟩ := eventually_atTop.mp hopen
  refine ⟨fun k => u (k+N),fun k => hN (k+N) (by omega),?_⟩
  exact hu.comp (tendsto_add_atTop_nat N)

namespace SourceLemma12_12Data
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The original angular domain contains arbitrarily small actual collapsed-gap
witnesses outside the Dirichlet segment. Exactly one signed extension is nonzero,
and a sequence of original open-gap sources converges to the witness. -/
theorem exists_original_collapsed_eta_witness (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (V : Set (CoeffPair p)) (hV : V ∈ 𝓝 (0 : CoeffPair p)) :
    ∃ a : ℂ, a ≠ 0 ∧ sourceConstantPotential (p := p) a 0 ∈ W ∩ V ∧
      sourceConstantPotential a 0 ∈ sourceDirichletOutsideGap hp hp1 W 0 ∧
      canonicalPeriodicGap hp hp1 (periodOnePotential (sourceConstantPotential a 0))
        (periodOnePotential_mem _) 0 = 0 ∧
      ((sourceGapWeightedEtaCoordinate hp hp1 0 s 1 (sourceConstantPotential a 0) = 0 ∧
        sourceGapWeightedEtaCoordinate hp hp1 0 s (-1) (sourceConstantPotential a 0) ≠ 0) ∨
       (sourceGapWeightedEtaCoordinate hp hp1 0 s 1 (sourceConstantPotential a 0) ≠ 0 ∧
        sourceGapWeightedEtaCoordinate hp hp1 0 s (-1) (sourceConstantPotential a 0) = 0)) ∧
      ∃ u : ℕ → CoeffPair p,
        (∀ k, u k ∈ W ∧ canonicalPeriodicGap hp hp1 (periodOnePotential (u k))
          (periodOnePotential_mem _) 0 ≠ 0) ∧
        Tendsto u atTop (𝓝 (sourceConstantPotential a 0)) := by
  let D := H.original_theta_common_domain
  have hW0 : (0 : CoeffPair p) ∈ W := D.real_subset (by simp [realTypeSourceLocus])
  obtain ⟨U,hU,hU0,hseq⟩ := exists_sourceConstant_open_gap_approach_neighborhood hp hp1
  obtain ⟨a,ha,haV,hL,hR,hμ⟩ := exists_sourceUpperConstant_collapsed_dirichlet_ne_zero
    hp hp1 ((W ∩ V) ∩ U)
    (inter_mem (inter_mem (D.source_open.mem_nhds hW0) hV) (hU.mem_nhds hU0))
  let φ := sourceConstantPotential (p := p) a 0
  have hg : canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem _) 0 = 0 := by
    simp only [canonicalPeriodicGap,φ,hL,hR,sub_self]
  have hm : sourceStandardRootMidpoint hp hp1 φ 0 = 0 := by
    simp only [sourceStandardRootMidpoint,canonicalPeriodicMidpoint,φ,hL,hR,zero_add,zero_div]
  have hout : φ ∈ sourceDirichletOutsideGap hp hp1 W 0 := by
    refine ⟨haV.1.1,?_⟩
    simpa only [sourcePeriodicSegment,φ,hL,hR,segment_same,mem_singleton_iff] using hμ
  refine ⟨a,ha,haV.1,hout,hg,?_,hseq a ha haV.2 W D.source_open haV.1.1⟩
  exact H.gapWeighted_original_collapsed_pair_exactly_one_nonzero φ haV.1.1 0 hg
    (by simpa only [hm] using hμ)

/-- At the constructed witness, the original signed phase expressions have actual
sequence limits, and exactly one of those two limits vanishes. -/
theorem exists_original_collapsed_eta_sequence_limits (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (V : Set (CoeffPair p)) (hV : V ∈ 𝓝 (0 : CoeffPair p)) :
    ∃ φ ∈ V ∩ sourceDirichletOutsideGap hp hp1 W 0,
      canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem _) 0 = 0 ∧
      ∃ u : ℕ → CoeffPair p,
        (∀ k, u k ∈ W ∧ canonicalPeriodicGap hp hp1 (periodOnePotential (u k))
          (periodOnePotential_mem _) 0 ≠ 0) ∧
        Tendsto u atTop (𝓝 φ) ∧
        (∀ σ : ℂ, σ = 1 ∨ σ = -1 →
          Tendsto (fun k => canonicalPeriodicGap hp hp1 (periodOnePotential (u k))
            (periodOnePotential_mem _) 0 *
            Complex.exp (σ*I*sourceAngularOriginalEta hp hp1 0 s (u k))) atTop
            (𝓝 (sourceGapWeightedEtaCoordinate hp hp1 0 s σ φ))) ∧
        ((sourceGapWeightedEtaCoordinate hp hp1 0 s 1 φ = 0 ∧
          sourceGapWeightedEtaCoordinate hp hp1 0 s (-1) φ ≠ 0) ∨
         (sourceGapWeightedEtaCoordinate hp hp1 0 s 1 φ ≠ 0 ∧
          sourceGapWeightedEtaCoordinate hp hp1 0 s (-1) φ = 0)) := by
  obtain ⟨a,_,ha,hout,hg,hs,u,hu,ht⟩ := H.exists_original_collapsed_eta_witness V hV
  refine ⟨sourceConstantPotential a 0,⟨ha.2,hout⟩,hg,u,hu,ht,?_,hs⟩
  intro σ hσ
  exact H.gapWeighted_original_phase_limit u _ ha.1 0 σ hσ ht (Eventually.of_forall hu)

/-- The printed assertion that both signs have nonzero collapsed values on F_0
is false on every retained original angular domain. -/
theorem original_collapsed_both_signed_values_nonzero_false
    (H : SourceLemma12_12Data hp hp1 W₀ W s) :
    ¬ (∀ φ ∈ sourceDirichletOutsideGap hp hp1 W 0,
      canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem _) 0 = 0 →
      sourceGapWeightedEtaCoordinate hp hp1 0 s 1 φ ≠ 0 ∧
      sourceGapWeightedEtaCoordinate hp hp1 0 s (-1) φ ≠ 0) := by
  intro hall
  obtain ⟨a,_,_,hout,hg,hs,_⟩ := H.exists_original_collapsed_eta_witness univ univ_mem
  have hn := hall (sourceConstantPotential a 0) hout hg
  rcases hs with h | h
  · exact hn.1 h.1
  · exact hn.2 h.2

end SourceLemma12_12Data
end NLS.ZakharovShabat
