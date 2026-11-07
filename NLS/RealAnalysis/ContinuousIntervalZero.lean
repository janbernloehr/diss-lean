import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.Order.Compact

/-! A unique zero selected in a moving compact real interval varies
continuously. Only endpoint continuity and continuity of the equation
at the limiting parameter are needed, including a collapsed interval. -/
noncomputable section
open Set Filter Topology
namespace NLS.RealAnalysis

variable {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]

theorem continuousAt_unique_zero_in_interval
    (F : ℝ × X → ℂ) (l r g : X → ℝ) (x : X)
    (hl : ContinuousAt l x) (hr : ContinuousAt r x)
    (hF : ∀ a : ℝ, ContinuousAt F (a,x))
    (hgap : ∀ y : X, g y ∈ Icc (l y) (r y))
    (hroot : ∀ y : X, F (g y,y) = 0)
    (hunique : ∀ a ∈ Icc (l x) (r x), F (a,x) = 0 → a = g x) : ContinuousAt g x := by
  change Tendsto g (𝓝 x) (𝓝 (g x))
  apply tendsto_iff_seq_tendsto.mpr
  intro u hu
  apply tendsto_of_subseq_tendsto
  intro ns hns
  let v : ℕ → X := u ∘ ns
  have hv : Tendsto v atTop (𝓝 x) := hu.comp hns
  have hleft := (hl.tendsto.comp hv).eventually (lt_mem_nhds (show l x-1 < l x by linarith))
  have hright := (hr.tendsto.comp hv).eventually (gt_mem_nhds (show r x < r x+1 by linarith))
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hleft.and hright)
  let w : ℕ → ℝ := fun k => g (v (k+N))
  have hw (k : ℕ) : w k ∈ Icc (l x-1) (r x+1) :=
    ⟨(hN (k+N) (by omega)).1.le.trans (hgap (v (k+N))).1,
      (hgap (v (k+N))).2.trans (hN (k+N) (by omega)).2.le⟩
  obtain ⟨a,_,σ,hσ,ha⟩ := (isCompact_Icc : IsCompact (Icc (l x-1) (r x+1))).tendsto_subseq hw
  have hsource : Tendsto (fun k => v (σ k+N)) atTop (𝓝 x) :=
    hv.comp ((tendsto_add_atTop_nat N).comp hσ.tendsto_atTop)
  have hmem : a ∈ Icc (l x) (r x) := by
    constructor
    · exact le_of_tendsto_of_tendsto (hl.tendsto.comp hsource) ha
        (Eventually.of_forall (fun k => (hgap (v (σ k+N))).1))
    · exact le_of_tendsto_of_tendsto ha (hr.tendsto.comp hsource)
        (Eventually.of_forall (fun k => (hgap (v (σ k+N))).2))
  have hzero : F (a,x) = 0 := by
    have ht := (hF a).tendsto.comp (ha.prodMk_nhds hsource)
    have hz : Tendsto (fun k => F (w (σ k),v (σ k+N))) atTop (𝓝 0) := by
      simpa only [w,hroot] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℂ)) atTop (𝓝 0))
    exact tendsto_nhds_unique ht hz
  have he := hunique a hmem hzero
  refine ⟨fun k => σ k+N,?_⟩
  simpa only [Function.comp_def,v,w,he] using ha

end NLS.RealAnalysis
