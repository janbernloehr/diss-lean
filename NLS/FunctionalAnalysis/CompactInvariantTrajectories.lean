import NLS.FunctionalAnalysis.CompactInvariantCurveContinuation

/-! Compatible local trajectories for compact conserved fibers.
Local C1 uniqueness assembles every trajectory through a fixed source
into one solution on the union of its open time intervals. -/
noncomputable section
open Set Metric Filter Topology
namespace NLS.FunctionalAnalysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {S : Type*}
namespace CompactInvariantVectorField
variable (D : CompactInvariantVectorField E S)

structure Trajectory (D : CompactInvariantVectorField E S) (q : E) where
  curve : ℝ → E
  lower : ℝ
  upper : ℝ
  initialTime_mem : (0 : ℝ) ∈ Ioo lower upper
  initialSource : curve 0=q
  hasDerivAt : ∀ t ∈ Ioo lower upper, HasDerivAt curve (D.field (curve t)) t

theorem nonempty_trajectory (q : E) : Nonempty (Trajectory D q) := by
  obtain ⟨γ,h0,ε,hε,hder⟩ :=
    D.contDiff.contDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ (x₀ := q) 0
  refine ⟨⟨γ,-ε,ε,⟨by linarith,hε⟩,h0,?_⟩⟩
  simpa only [zero_sub,zero_add] using hder

def timeDomain (q : E) : Set ℝ :=
  {t | ∃ T : Trajectory D q, t ∈ Ioo T.lower T.upper}

theorem zero_mem_timeDomain (q : E) : (0 : ℝ) ∈ D.timeDomain q := by
  obtain ⟨T⟩ := D.nonempty_trajectory q
  exact ⟨T,T.initialTime_mem⟩

omit [CompleteSpace E] in
theorem isOpen_timeDomain (q : E) : IsOpen (D.timeDomain q) := by
  rw [isOpen_iff_eventually]
  rintro t ⟨T,ht⟩
  filter_upwards [isOpen_Ioo.eventually_mem ht] with u hu
  exact ⟨T,hu⟩

omit [CompleteSpace E] in
theorem ordConnected_timeDomain (q : E) : OrdConnected (D.timeDomain q) := by
  constructor
  rintro u ⟨T,hu⟩ v ⟨U,hv⟩ t ht
  by_cases hneg : t < 0
  · exact ⟨T,⟨hu.1.trans_le ht.1,hneg.trans T.initialTime_mem.2⟩⟩
  · exact ⟨U,⟨U.initialTime_mem.1.trans_le (not_lt.mp hneg),ht.2.trans_lt hv.2⟩⟩

def globalCurve (q : E) (t : ℝ) : E := by
  classical
  exact if h : t ∈ D.timeDomain q then h.choose.curve t else q

omit [CompleteSpace E] in
theorem globalCurve_eqOn_trajectory (q : E) (T : Trajectory D q) :
    EqOn (D.globalCurve q) T.curve (Ioo T.lower T.upper) := by
  intro t ht
  have hmem : t ∈ D.timeDomain q := ⟨T,ht⟩
  rw [globalCurve,dif_pos hmem]
  let U := hmem.choose
  have hU : t ∈ Ioo U.lower U.upper := hmem.choose_spec
  apply eqOn_integralCurves_of_contDiffAt D.field U.curve T.curve
    (Ioo U.lower U.upper ∩ Ioo T.lower T.upper) (isOpen_Ioo.inter isOpen_Ioo)
    ((convex_Ioo U.lower U.upper).inter (convex_Ioo T.lower T.upper)).isPreconnected
    (fun s hs => U.hasDerivAt s hs.1) (fun s hs => T.hasDerivAt s hs.2)
    (fun _ _ => D.contDiff.contDiffAt) 0 ⟨U.initialTime_mem,T.initialTime_mem⟩
    (U.initialSource.trans T.initialSource.symm) ⟨hU,ht⟩

theorem globalCurve_zero (q : E) : D.globalCurve q 0=q := by
  obtain ⟨T⟩ := D.nonempty_trajectory q
  exact (D.globalCurve_eqOn_trajectory q T T.initialTime_mem).trans T.initialSource

omit [CompleteSpace E] in
theorem hasDerivAt_globalCurve_of_mem (q : E) (t : ℝ) (ht : t ∈ D.timeDomain q) :
    HasDerivAt (D.globalCurve q) (D.field (D.globalCurve q t)) t := by
  obtain ⟨T,hT⟩ := ht
  have heq := D.globalCurve_eqOn_trajectory q T
  rw [heq hT]
  apply (T.hasDerivAt t hT).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.eventually_mem hT] with u hu
  exact heq hu

end CompactInvariantVectorField
end NLS.FunctionalAnalysis
