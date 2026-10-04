import NLS.SequenceSpaces.HeadActionPathAnalytic
import Mathlib.Topology.Compactness.Compact

/-! # A common neighborhood for complete head-action paths

The path is constant at the base. Compactness of the unit interval gives
one neighborhood of initial points on which the whole path stays in the
prescribed open domain, remains analytic, and has no zero retained pair.
-/
noncomputable section
open Set Metric Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {q : ℝ≥0∞} [Fact (1 ≤ q)]

/-- Uniform path control over the complete unit interval. -/
theorem exists_headActionPath_neighborhood (S : Finset ℤ) (a : TailSumSpace q S)
    (ha : HeadNonzero S a) (U : Set (TailSumSpace q S)) (hU : IsOpen U) (haU : a ∈ U) :
    ∃ V : Set (TailSumSpace q S), IsOpen V ∧ a ∈ V ∧ V ⊆ U ∧
      ∀ w ∈ V, headActionPath S a (w,0) = w ∧
        ∀ t ∈ Icc (0 : ℝ) 1,
          AnalyticAt ℂ (headActionPath S a) (w,(t : ℂ)) ∧
          headActionPath S a (w,(t : ℂ)) ∈ U ∧ HeadNonzero S (headActionPath S a (w,(t : ℂ))) := by
  let good : Set (TailSumSpace q S × ℂ) := {u | AnalyticAt ℂ (headActionPath S a) u ∧
    headActionPath S a u ∈ U ∧ HeadNonzero S (headActionPath S a u)}
  have hbase (t : ℂ) : (a,t) ∈ interior good := by
    have hp := analyticAt_headActionPath_base S a ha t
    have hstay : ∀ᶠ u in 𝓝 (a,t), headActionPath S a u ∈ U :=
      hp.continuousAt.preimage_mem_nhds (by simpa only [headActionPath_base S a ha t] using hU.mem_nhds haU)
    have hn : ∀ᶠ u in 𝓝 (a,t), HeadNonzero S (headActionPath S a u) := by
      have he (k : S) : ∀ᶠ u in 𝓝 (a,t), headActionSolved S a (headActionPath S a u) k ≠ 0 := by
        have hc := (analyticAt_headActionSolved S a (headActionPath S a (a,t)) k).continuousAt.comp hp.continuousAt
        apply hc.eventually_ne
        simpa only [Function.comp_def,headActionPath_base S a ha t] using headActionSolved_ne_zero S a ha k
      filter_upwards [Filter.eventually_all.mpr he] with u hu
      intro k
      by_cases hx : a.1 k ≠ 0
      · left
        simpa only [headActionSolved,if_pos hx] using hu k
      · right
        simpa only [headActionSolved,if_neg hx] using hu k
    exact mem_interior_iff_mem_nhds.mpr (hp.eventually_analyticAt.and (hstay.and hn))
  let K : Set ℂ := (fun t : ℝ => (t : ℂ)) '' Icc (0 : ℝ) 1
  have hK : IsCompact K := isCompact_Icc.image Complex.continuous_ofReal
  have hprod : ({a} : Set (TailSumSpace q S)) ×ˢ K ⊆ interior good := by
    rintro ⟨w,t⟩ ⟨hw,_⟩
    have hw' : w = a := mem_singleton_iff.mp hw
    subst w
    exact hbase t
  obtain ⟨W,J,hW,_,haW,hKJ,hinto⟩ := generalized_tube_lemma isCompact_singleton hK isOpen_interior hprod
  obtain ⟨O,hOsub,hO,haO⟩ := _root_.mem_nhds_iff.mp (eventually_headActionPath_zero S a ha)
  have hgood (w : TailSumSpace q S) (hw : w ∈ W) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (w,(t : ℂ)) ∈ good :=
    interior_subset (hinto ⟨hw,hKJ ⟨t,ht,rfl⟩⟩)
  refine ⟨W ∩ O,hW.inter hO,⟨haW (mem_singleton a),haO⟩,?_,?_⟩
  · intro w hw
    have he := (hgood w hw.1 0 (by simp)).2.1
    have hstart : headActionPath S a (w,0) = w := hOsub hw.2
    simpa only [Complex.ofReal_zero,hstart] using he
  · intro w hw
    exact ⟨hOsub hw.2,fun t ht => hgood w hw.1 t ht⟩

end NLS.Coeff
