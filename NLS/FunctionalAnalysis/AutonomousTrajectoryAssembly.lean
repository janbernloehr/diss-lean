import NLS.FunctionalAnalysis.AutonomousODEUniqueness

noncomputable section
set_option autoImplicit false
open Set Metric Filter Topology
open scoped Classical

namespace NLS.FunctionalAnalysis



variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An actual autonomous trajectory through a fixed initial value on an
open time interval containing zero. -/
structure AutonomousTrajectory (V : E → E) (q : E) where
  curve : ℝ → E
  lower : ℝ
  upper : ℝ
  initialTime_mem : (0 : ℝ)∈Ioo lower upper
  initialSource : curve 0=q
  hasDerivAt : ∀ t∈Ioo lower upper, HasDerivAt curve (V (curve t)) t

/-- All times covered by an actual trajectory through the initial value. -/
def autonomousTrajectoryTimeDomain (V : E → E) (q : E) : Set ℝ :=
  {t | ∃ T : AutonomousTrajectory V q, t∈Ioo T.lower T.upper}

theorem zero_mem_autonomousTrajectoryTimeDomain (V : E → E) (q : E)
    (hlocal : Nonempty (AutonomousTrajectory V q)) :
    (0 : ℝ)∈autonomousTrajectoryTimeDomain V q := by
  obtain ⟨T⟩ := hlocal
  exact ⟨T,T.initialTime_mem⟩

theorem isOpen_autonomousTrajectoryTimeDomain (V : E → E) (q : E) :
    IsOpen (autonomousTrajectoryTimeDomain V q) := by
  rw [isOpen_iff_eventually]
  rintro t ⟨T,ht⟩
  filter_upwards [isOpen_Ioo.eventually_mem ht] with u hu
  exact ⟨T,hu⟩

/-- The compatible time domain is one interval, since every constituent
trajectory interval contains the same initial time. -/
theorem ordConnected_autonomousTrajectoryTimeDomain (V : E → E) (q : E) :
    OrdConnected (autonomousTrajectoryTimeDomain V q) := by
  constructor
  rintro u ⟨T,hu⟩ v ⟨U,hv⟩ t ht
  by_cases hneg : t<0
  · exact ⟨T,⟨hu.1.trans_le ht.1,hneg.trans T.initialTime_mem.2⟩⟩
  · exact ⟨U,⟨U.initialTime_mem.1.trans_le (not_lt.mp hneg),ht.2.trans_lt hv.2⟩⟩

/-- Assemble compatible actual trajectories; the initial source is used
only at times not yet known to be covered by a trajectory. -/
def assembledAutonomousTrajectory (V : E → E) (q : E) (t : ℝ) : E :=
  if h : t∈autonomousTrajectoryTimeDomain V q then h.choose.curve t else q

/-- Actual local uniqueness makes the assembly agree with every original
trajectory on its entire interval. -/
theorem assembledAutonomousTrajectory_eqOn (V : E → E) (q : E)
    (hV : ContDiff ℝ 1 V) (T : AutonomousTrajectory V q) :
    EqOn (assembledAutonomousTrajectory V q) T.curve (Ioo T.lower T.upper) := by
  intro t ht
  have hmem : t∈autonomousTrajectoryTimeDomain V q := ⟨T,ht⟩
  rw [assembledAutonomousTrajectory,dif_pos hmem]
  let U := hmem.choose
  have hU : t∈Ioo U.lower U.upper := hmem.choose_spec
  have heq := eqOn_of_autonomous_hasDerivAt (isOpen_Ioo.inter isOpen_Ioo)
    ((convex_Ioo U.lower U.upper).inter (convex_Ioo T.lower T.upper)).isPreconnected
    (fun _ _ => hV.contDiffAt) (fun r hr => U.hasDerivAt r hr.1)
    (fun r hr => T.hasDerivAt r hr.2) ⟨U.initialTime_mem,T.initialTime_mem⟩
    (U.initialSource.trans T.initialSource.symm)
  exact heq ⟨hU,ht⟩

theorem assembledAutonomousTrajectory_zero (V : E → E) (q : E)
    (hV : ContDiff ℝ 1 V) (hlocal : Nonempty (AutonomousTrajectory V q)) :
    assembledAutonomousTrajectory V q 0=q := by
  obtain ⟨T⟩ := hlocal
  exact (assembledAutonomousTrajectory_eqOn V q hV T T.initialTime_mem).trans T.initialSource

/-- Neighborhood agreement transfers the actual differential equation
from a representative to the assembled trajectory. -/
theorem hasDerivAt_assembledAutonomousTrajectory_of_mem (V : E → E) (q : E)
    (hV : ContDiff ℝ 1 V) (t : ℝ) (ht : t∈autonomousTrajectoryTimeDomain V q) :
    HasDerivAt (assembledAutonomousTrajectory V q) (V (assembledAutonomousTrajectory V q t)) t := by
  obtain ⟨T,hT⟩ := ht
  have heq := assembledAutonomousTrajectory_eqOn V q hV T
  rw [heq hT]
  apply (T.hasDerivAt t hT).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.eventually_mem hT] with u hu
  exact heq hu

end NLS.FunctionalAnalysis
