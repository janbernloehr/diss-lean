import NLS.FunctionalAnalysis.AutonomousTrajectoryAssembly

noncomputable section
set_option autoImplicit false
open Set Metric Filter Topology
open scoped Classical

namespace NLS.FunctionalAnalysis



variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Every actual trajectory through a fixed source can be continued past
both finite time endpoints while retaining every old trajectory value. -/
structure AutonomousEndpointExtensions (V : E → E) (q : E) : Prop where
  right : ∀ T : AutonomousTrajectory V q,
    ∃ ε : ℝ, 0<ε ∧ ∃ Γ : ℝ → E, EqOn Γ T.curve (Ioo T.lower T.upper) ∧
      ∀ t∈Ioo T.lower (T.upper+ε), HasDerivAt Γ (V (Γ t)) t
  left : ∀ T : AutonomousTrajectory V q,
    ∃ ε : ℝ, 0<ε ∧ ∃ Γ : ℝ → E, EqOn Γ T.curve (Ioo T.lower T.upper) ∧
      ∀ t∈Ioo (T.lower-ε) T.upper, HasDerivAt Γ (V (Γ t)) t

private theorem exists_neg_pos_in_domain (V : E → E) (q : E)
    (hlocal : Nonempty (AutonomousTrajectory V q)) :
    ∃ a b : ℝ, a<0 ∧ 0<b ∧ a∈autonomousTrajectoryTimeDomain V q ∧ b∈autonomousTrajectoryTimeDomain V q := by
  obtain ⟨T⟩ := hlocal
  have hL := T.initialTime_mem.1
  have hR := T.initialTime_mem.2
  refine ⟨T.lower/2,T.upper/2,by linarith,by linarith,⟨T,?_⟩,⟨T,?_⟩⟩ <;>
    constructor <;> linarith

/-- Actual uniqueness and actual continuation rule out every finite endpoint
of the assembled time domain; hence it is the whole real line. -/
theorem autonomousTrajectoryTimeDomain_eq_univ_of_extensions
    (V : E → E) (q : E) (hV : ContDiff ℝ 1 V)
    (hlocal : Nonempty (AutonomousTrajectory V q)) (hExt : AutonomousEndpointExtensions V q) :
    autonomousTrajectoryTimeDomain V q=univ := by
  let D := autonomousTrajectoryTimeDomain V q
  have hzero := assembledAutonomousTrajectory_zero V q hV hlocal
  have hAbove : ¬BddAbove D := by
    intro hbd
    obtain ⟨a,r,ha0,hr0,ha,hr⟩ := exists_neg_pos_in_domain V q hlocal
    have hne : D.Nonempty := ⟨a,ha⟩
    let b := sSup D
    have hb0 : 0<b := hr0.trans_le (le_csSup hbd hr)
    have hsub : Ioo a b⊆D := by
      intro t ht
      obtain ⟨s,hs,hts⟩ := (lt_csSup_iff hbd hne).mp ht.2
      exact (ordConnected_autonomousTrajectoryTimeDomain V q).out ha hs ⟨ht.1.le,hts.le⟩
    let T : AutonomousTrajectory V q :=
      ⟨assembledAutonomousTrajectory V q,a,b,⟨ha0,hb0⟩,hzero,
        fun t ht => hasDerivAt_assembledAutonomousTrajectory_of_mem V q hV t (hsub ht)⟩
    obtain ⟨ε,hε,Γ,hEq,hD⟩ := hExt.right T
    have h0 : (0 : ℝ)∈Ioo a b := ⟨ha0,hb0⟩
    let T' : AutonomousTrajectory V q :=
      ⟨Γ,a,b+ε,⟨ha0,by linarith⟩,(hEq h0).trans hzero,hD⟩
    have ht : b+ε/2∈D := ⟨T',⟨by dsimp only [T'];linarith,by dsimp only [T'];linarith⟩⟩
    have hh : b+ε/2≤b := le_csSup hbd ht
    linarith
  have hBelow : ¬BddBelow D := by
    intro hbd
    obtain ⟨r,b,hr0,hb0,hr,hb⟩ := exists_neg_pos_in_domain V q hlocal
    have hne : D.Nonempty := ⟨b,hb⟩
    let a := sInf D
    have ha0 : a<0 := (csInf_le hbd hr).trans_lt hr0
    have hsub : Ioo a b⊆D := by
      intro t ht
      obtain ⟨s,hs,hst⟩ := (csInf_lt_iff hbd hne).mp ht.1
      exact (ordConnected_autonomousTrajectoryTimeDomain V q).out hs hb ⟨hst.le,ht.2.le⟩
    let T : AutonomousTrajectory V q :=
      ⟨assembledAutonomousTrajectory V q,a,b,⟨ha0,hb0⟩,hzero,
        fun t ht => hasDerivAt_assembledAutonomousTrajectory_of_mem V q hV t (hsub ht)⟩
    obtain ⟨ε,hε,Γ,hEq,hD⟩ := hExt.left T
    have h0 : (0 : ℝ)∈Ioo a b := ⟨ha0,hb0⟩
    let T' : AutonomousTrajectory V q :=
      ⟨Γ,a-ε,b,⟨by linarith,hb0⟩,(hEq h0).trans hzero,hD⟩
    have ht : a-ε/2∈D := ⟨T',⟨by dsimp only [T'];linarith,by dsimp only [T'];linarith⟩⟩
    have hh : a≤a-ε/2 := csInf_le hbd ht
    linarith
  apply eq_univ_of_forall
  intro t
  obtain ⟨a,ha,hat⟩ := not_bddBelow_iff.mp hBelow t
  obtain ⟨b,hb,htb⟩ := not_bddAbove_iff.mp hAbove t
  exact (ordConnected_autonomousTrajectoryTimeDomain V q).out ha hb ⟨hat.le,htb.le⟩

/-- A smooth autonomous field with a local trajectory and proved finite
endpoint continuation has an actual trajectory for all real times. -/
theorem exists_global_autonomousTrajectory_of_endpointExtensions
    (V : E → E) (q : E) (hV : ContDiff ℝ 1 V)
    (hlocal : Nonempty (AutonomousTrajectory V q)) (hExt : AutonomousEndpointExtensions V q) :
    ∃ γ : ℝ → E, γ 0=q ∧ ∀ t : ℝ, HasDerivAt γ (V (γ t)) t := by
  refine ⟨assembledAutonomousTrajectory V q,assembledAutonomousTrajectory_zero V q hV hlocal,?_⟩
  intro t
  apply hasDerivAt_assembledAutonomousTrajectory_of_mem V q hV t
  rw [autonomousTrajectoryTimeDomain_eq_univ_of_extensions V q hV hlocal hExt]
  exact mem_univ t

end NLS.FunctionalAnalysis
