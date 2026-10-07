import NLS.ZakharovShabat.SourceSobolevActionBound
import NLS.ZakharovShabat.SourceSymmetricContour
import NLS.SequenceSpaces.LocallyBoundedRealization

/-! # Analytic weighted spectral-action sum near real H¹ sources

Local ℓ¹ bounds assemble the actual analytic scalar actions into one analytic
sequence map. Bounded summation gives the physical weighted-action subtraction,
with an absolutely convergent literal series on an open complex H¹ neighborhood
of the entire real source locus.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The actual kinetic-weighted actions, whenever they are summable. The theorems
below rule out the constructor's fallback near every real H¹ source. -/
def sourceSobolevWeightedActionSequence (a : ScalarDomain 2 × ScalarDomain 2) : Coeff 1 :=
  Coeff.ofFunctionOrZero 1 (sourceSobolevWeightedAction a)

/-- The weighted spectral term in the physical Hamiltonian correction. -/
def sourceSobolevWeightedActionSum (a : ScalarDomain 2 × ScalarDomain 2) : ℂ :=
  lp.tsumCLM ℂ ℤ ℂ (sourceSobolevWeightedActionSequence a)

/-- One complex H¹ neighborhood carries the actual ℓ¹ sequence and its Banach analytic map. -/
theorem exists_local_sourceSobolevWeightedActionSequence_analytic
    (a : ScalarDomain 2 × ScalarDomain 2)
    (ha : IsRealType (CoeffPair.toMax 2 (sobolevSourceInclusion a))) :
    ∃ U : Set (ScalarDomain 2 × ScalarDomain 2), IsOpen U ∧ a ∈ U ∧
      (∀ b ∈ U, ∀ n : ℤ, sourceSobolevWeightedActionSequence b n = sourceSobolevWeightedAction b n) ∧
      AnalyticOnNhd ℂ sourceSobolevWeightedActionSequence U := by
  let L := sobolevSourceInclusion
  obtain ⟨V,hV,haV,C,hbound⟩ := exists_local_sourceSobolevWeightedAction_bound a ha
  obtain ⟨W,hW,_,hrealW,hMG⟩ :=
    exists_global_source_analytic_midpoint_squaredGap (by simp : (2 : ℝ≥0∞) ≠ ⊤) (by norm_num)
  obtain ⟨T,hT,haT,hfactorA,hfactor⟩ := exists_local_sourceNormalizedAction_allIndices_analytic_factor
    (by simp) (by norm_num) (L a) ha
  let U := V ∩ L ⁻¹' (W ∩ T)
  have hU : IsOpen U := hV.inter ((hW.inter hT).preimage L.continuous)
  have he (b : ScalarDomain 2 × ScalarDomain 2) (hb : b ∈ U) :
      ∀ n, sourceSobolevWeightedActionSequence b n = sourceSobolevWeightedAction b n := by
    obtain ⟨g,hg,_⟩ := hbound b hb.1
    rw [sourceSobolevWeightedActionSequence, Coeff.ofFunctionOrZero_eq_of_coordinates _ g hg]
    exact hg
  refine ⟨U,hU,⟨haV,hrealW ha,haT⟩,he,?_⟩
  refine Coeff.analyticOnNhd_of_bounded_coordinatewise _ hU ?_ C ?_
  · intro n b hb
    have hgap : AnalyticAt ℂ (fun c : ScalarDomain 2 × ScalarDomain 2 =>
        (sourcePeriodicGapDisplacement (by simp) (by norm_num) (L c) n)^2) b := by
      simpa only [sourcePeriodicGapDisplacement_apply] using!
        ((hMG (L b) hb.2.1 n).2.comp (L.analyticAt b))
    have hA := (hfactorA n (L b) hb.2.2).comp (L.analyticAt b)
    have h : AnalyticAt ℂ (fun c : ScalarDomain 2 × ScalarDomain 2 =>
        (2*(Real.pi : ℂ)*n)^2 *
          ((sourcePeriodicGapDisplacement (by simp) (by norm_num) (L c) n)^2 *
            sourceNormalizedActionComplexExtension (by simp) (by norm_num) n (L c))) b :=
      analyticAt_const.mul (hgap.mul hA)
    apply h.congr
    filter_upwards [hU.mem_nhds hb] with c hc
    rw [he c hc n, sourceSobolevWeightedAction, hfactor (L c) hc.2.2 n]
  · intro b hb
    obtain ⟨g,hg,hgn⟩ := hbound b hb.1
    rwa [sourceSobolevWeightedActionSequence, Coeff.ofFunctionOrZero_eq_of_coordinates _ g hg]

/-- One open complex H¹ domain contains all real sources and carries the analytic
weighted-action sequence and its absolutely convergent scalar sum. -/
theorem exists_sourceSobolevWeightedAction_analytic_domain :
    ∃ U : Set (ScalarDomain 2 × ScalarDomain 2), IsOpen U ∧
      {a | IsRealType (CoeffPair.toMax 2 (sobolevSourceInclusion a))} ⊆ U ∧
      (∀ a ∈ U, ∀ n : ℤ, sourceSobolevWeightedActionSequence a n = sourceSobolevWeightedAction a n) ∧
      AnalyticOnNhd ℂ sourceSobolevWeightedActionSequence U ∧
      AnalyticOnNhd ℂ sourceSobolevWeightedActionSum U ∧
      ∀ a ∈ U, Summable (fun n : ℤ => ‖sourceSobolevWeightedAction a n‖) ∧
        sourceSobolevWeightedActionSum a = ∑' n : ℤ, sourceSobolevWeightedAction a n := by
  classical
  let R := {a : ScalarDomain 2 × ScalarDomain 2 //
    IsRealType (CoeffPair.toMax 2 (sobolevSourceInclusion a))}
  have hlocal (a : R) := exists_local_sourceSobolevWeightedActionSequence_analytic a.val a.property
  choose V hV haV hcoord hA using hlocal
  let U := ⋃ a : R, V a
  have he (a : ScalarDomain 2 × ScalarDomain 2) (ha : a ∈ U) (n : ℤ) :
      sourceSobolevWeightedActionSequence a n = sourceSobolevWeightedAction a n := by
    obtain ⟨b,hb⟩ := mem_iUnion.mp ha
    exact hcoord b a hb n
  have hseq : AnalyticOnNhd ℂ sourceSobolevWeightedActionSequence U := by
    intro a ha
    obtain ⟨b,hb⟩ := mem_iUnion.mp ha
    exact hA b a hb
  refine ⟨U,isOpen_iUnion hV,?_,he,hseq,
    (lp.tsumCLM ℂ ℤ ℂ).comp_analyticOnNhd hseq,?_⟩
  · intro a ha
    exact mem_iUnion_of_mem (⟨a,ha⟩ : R) (haV ⟨a,ha⟩)
  · intro a ha
    have hs := (sourceSobolevWeightedActionSequence a).property.norm.summable_of_one
    refine ⟨?_,?_⟩
    · simpa only [he a ha] using hs
    · exact tsum_congr (he a ha)

/-- In particular, the literal weighted action series is absolutely summable at every real H¹ source. -/
theorem summable_norm_sourceSobolevWeightedAction
    (a : ScalarDomain 2 × ScalarDomain 2)
    (ha : IsRealType (CoeffPair.toMax 2 (sobolevSourceInclusion a))) :
    Summable (fun n : ℤ => ‖sourceSobolevWeightedAction a n‖) := by
  obtain ⟨_,_,hr,_,_,_,hs⟩ := exists_sourceSobolevWeightedAction_analytic_domain
  exact (hs a (hr ha)).1

theorem sourceSobolevWeightedActionSum_eq_tsum
    (a : ScalarDomain 2 × ScalarDomain 2)
    (ha : IsRealType (CoeffPair.toMax 2 (sobolevSourceInclusion a))) :
    sourceSobolevWeightedActionSum a = ∑' n : ℤ, sourceSobolevWeightedAction a n := by
  obtain ⟨_,_,hr,_,_,_,hs⟩ := exists_sourceSobolevWeightedAction_analytic_domain
  exact (hs a (hr ha)).2

theorem analyticAt_sourceSobolevWeightedActionSum
    (a : ScalarDomain 2 × ScalarDomain 2)
    (ha : IsRealType (CoeffPair.toMax 2 (sobolevSourceInclusion a))) :
    AnalyticAt ℂ sourceSobolevWeightedActionSum a := by
  obtain ⟨_,_,hr,_,_,hA,_⟩ := exists_sourceSobolevWeightedAction_analytic_domain
  exact hA a (hr ha)

/-- The literal infinite spectral sum itself is analytic near every real H¹ source. -/
theorem analyticAt_tsum_sourceSobolevWeightedAction
    (a : ScalarDomain 2 × ScalarDomain 2)
    (ha : IsRealType (CoeffPair.toMax 2 (sobolevSourceInclusion a))) :
    AnalyticAt ℂ (fun b : ScalarDomain 2 × ScalarDomain 2 =>
      ∑' n : ℤ, sourceSobolevWeightedAction b n) a := by
  obtain ⟨U,hU,hr,_,_,hA,hs⟩ := exists_sourceSobolevWeightedAction_analytic_domain
  apply (hA a (hr ha)).congr
  filter_upwards [hU.mem_nhds (hr ha)] with b hb
  exact (hs b hb).2

end NLS.ZakharovShabat
