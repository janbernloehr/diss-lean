import NLS.FunctionalAnalysis.SymmetricPencilEstimate

/-! # Closed range from a lower bound for a closed partial operator

The domain need not be complete in its inherited norm. Instead, the
lower bound makes preimages Cauchy in the base Hilbert space, and closedness
of the original graph recovers the limiting domain element.
-/
noncomputable section
set_option autoImplicit false
open Set Filter
open scoped Topology
namespace NLS.FunctionalAnalysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- A positive lower bound for the pencil of a closed operator gives closed range. -/
theorem isClosed_range_linearPMapPencil {T : E →ₗ.[ℂ] E}
    (hc : T.IsClosed) (z : ℂ) (c : ℝ) (hcpos : 0 < c)
    (hb : ∀ x : T.domain, c * ‖(x : E)‖ ≤ ‖linearPMapPencil T z x‖) :
    IsClosed (Set.range (linearPMapPencil T z)) := by
  apply IsSeqClosed.isClosed
  intro y l hy hyl
  choose x hx using hy
  have hcy : CauchySeq y := hyl.cauchySeq
  have hcx : CauchySeq (fun n => (x n : E)) := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp hcy (c*ε) (mul_pos hcpos hε)
    refine ⟨N,fun m hm n hn => ?_⟩
    have h := hb (x m-x n)
    rw [map_sub,hx m,hx n] at h
    change c * ‖(x m : E)-(x n : E)‖ ≤ ‖y m-y n‖ at h
    have hd := hN m hm n hn
    rw [dist_eq_norm] at hd ⊢
    nlinarith
  obtain ⟨v,hv⟩ := cauchySeq_tendsto_of_complete hcx
  have hTv : Tendsto (fun n => T (x n)) atTop (𝓝 (z • v-l)) := by
    have ht := (hv.const_smul z).sub hyl
    convert! ht using 1
    ext n
    have hn := hx n
    rw [linearPMapPencil_apply] at hn
    exact eq_sub_iff_add_eq.mpr (by rw [← hn]; module)
  have hg : (v,z • v-l) ∈ T.graph :=
    hc.mem_of_tendsto (hv.prodMk_nhds hTv) (Eventually.of_forall fun n => T.mem_graph (x n))
  obtain ⟨a,ha,hat⟩ := (T.mem_graph_iff).mp hg
  refine ⟨a,?_⟩
  rw [linearPMapPencil_apply,ha,hat]
  module

/-- Nonreal pencils of closed symmetric operators have closed range. -/
theorem isClosed_range_linearPMapPencil_of_im_ne_zero {T : E →ₗ.[ℂ] E}
    (hc : T.IsClosed) (hs : T.IsFormalAdjoint T) (z : ℂ) (hz : z.im ≠ 0) :
    IsClosed (Set.range (linearPMapPencil T z)) :=
  isClosed_range_linearPMapPencil hc z |z.im| (abs_pos.mpr hz)
    (norm_linearPMapPencil_ge_im hs z)

end NLS.FunctionalAnalysis
