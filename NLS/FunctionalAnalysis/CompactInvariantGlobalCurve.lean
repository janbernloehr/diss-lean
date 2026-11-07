import NLS.FunctionalAnalysis.CompactInvariantTrajectories

/-! Global completeness of a C1 Banach vector field with compact
conserved fibers. A finite endpoint of the compatible time domain
contradicts the constructed finite endpoint continuation. -/
noncomputable section
open Set Metric Filter Topology
namespace NLS.FunctionalAnalysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {S : Type*}
namespace CompactInvariantVectorField
variable (D : CompactInvariantVectorField E S)

theorem exists_neg_pos_mem_timeDomain (q : E) :
    ∃ a b : ℝ, a < 0 ∧ 0 < b ∧ a ∈ D.timeDomain q ∧ b ∈ D.timeDomain q := by
  obtain ⟨T⟩ := D.nonempty_trajectory q
  have hL := T.initialTime_mem.1
  have hR := T.initialTime_mem.2
  refine ⟨T.lower/2,T.upper/2,by linarith,by linarith,⟨T,?_⟩,⟨T,?_⟩⟩ <;>
    constructor <;> linarith

theorem not_bddAbove_timeDomain (q : E) : ¬BddAbove (D.timeDomain q) := by
  let U := D.timeDomain q
  change ¬BddAbove U
  intro hbd
  obtain ⟨a,r,ha0,hr0,ha,hr⟩ := D.exists_neg_pos_mem_timeDomain q
  have hne : U.Nonempty := ⟨a,ha⟩
  let b := sSup U
  have hb0 : 0 < b := hr0.trans_le (le_csSup hbd hr)
  have hsub : Ioo a b ⊆ U := by
    intro t ht
    obtain ⟨s,hs,hts⟩ := (lt_csSup_iff hbd hne).mp ht.2
    exact (D.ordConnected_timeDomain q).out ha hs ⟨ht.1.le,hts.le⟩
  have hder : ∀ t ∈ Ioo a b, HasDerivAt (D.globalCurve q) (D.field (D.globalCurve q t)) t :=
    fun t ht => D.hasDerivAt_globalCurve_of_mem q t (hsub ht)
  obtain ⟨ε,hε,Γ,hEq,hΓ⟩ := D.exists_rightContinuation (D.globalCurve q) a b (ha0.trans hb0) hder
  have h0 : (0 : ℝ) ∈ Ioo a b := ⟨ha0,hb0⟩
  let T : Trajectory D q :=
    ⟨Γ,a,b+ε,⟨ha0,by linarith⟩,(hEq h0).trans (D.globalCurve_zero q),hΓ⟩
  have ht : b+ε/2 ∈ U := ⟨T,⟨by dsimp [T]; linarith,by dsimp [T]; linarith⟩⟩
  have hle : b+ε/2 ≤ b := le_csSup hbd ht
  linarith

theorem not_bddBelow_timeDomain (q : E) : ¬BddBelow (D.timeDomain q) := by
  let U := D.timeDomain q
  change ¬BddBelow U
  intro hbd
  obtain ⟨r,b,hr0,hb0,hr,hb⟩ := D.exists_neg_pos_mem_timeDomain q
  have hne : U.Nonempty := ⟨b,hb⟩
  let a := sInf U
  have ha0 : a < 0 := (csInf_le hbd hr).trans_lt hr0
  have hsub : Ioo a b ⊆ U := by
    intro t ht
    obtain ⟨s,hs,hst⟩ := (csInf_lt_iff hbd hne).mp ht.1
    exact (D.ordConnected_timeDomain q).out hs hb ⟨hst.le,ht.2.le⟩
  have hder : ∀ t ∈ Ioo a b, HasDerivAt (D.globalCurve q) (D.field (D.globalCurve q t)) t :=
    fun t ht => D.hasDerivAt_globalCurve_of_mem q t (hsub ht)
  obtain ⟨ε,hε,Γ,hEq,hΓ⟩ := D.exists_leftContinuation (D.globalCurve q) a b (ha0.trans hb0) hder
  have h0 : (0 : ℝ) ∈ Ioo a b := ⟨ha0,hb0⟩
  let T : Trajectory D q :=
    ⟨Γ,a-ε,b,⟨by linarith,hb0⟩,(hEq h0).trans (D.globalCurve_zero q),hΓ⟩
  have ht : a-ε/2 ∈ U := ⟨T,⟨by dsimp [T]; linarith,by dsimp [T]; linarith⟩⟩
  have hle : a ≤ a-ε/2 := csInf_le hbd ht
  linarith

theorem timeDomain_eq_univ (q : E) : D.timeDomain q=univ := by
  apply eq_univ_of_forall
  intro t
  obtain ⟨a,ha,hat⟩ := not_bddBelow_iff.mp (D.not_bddBelow_timeDomain q) t
  obtain ⟨b,hb,htb⟩ := not_bddAbove_iff.mp (D.not_bddAbove_timeDomain q) t
  exact (D.ordConnected_timeDomain q).out ha hb ⟨hat.le,htb.le⟩

theorem hasDerivAt_globalCurve (q : E) (t : ℝ) :
    HasDerivAt (D.globalCurve q) (D.field (D.globalCurve q t)) t :=
  D.hasDerivAt_globalCurve_of_mem q t (by rw [D.timeDomain_eq_univ]; exact mem_univ _)

theorem globalCurve_conserved (q : E) (t : ℝ) : D.invariant (D.globalCurve q t)=D.invariant q := by
  let a : ℝ := min t 0-1
  let b : ℝ := max t 0+1
  have ht : t ∈ Ioo a b := ⟨by dsimp [a]; linarith [min_le_left t 0],
    by dsimp [b]; linarith [le_max_left t 0]⟩
  have h0 : (0 : ℝ) ∈ Ioo a b := ⟨by dsimp [a]; linarith [min_le_right t 0],
    by dsimp [b]; linarith [le_max_right t 0]⟩
  simpa only [D.globalCurve_zero] using
    D.conserved (D.globalCurve q) a b (fun s _ => D.hasDerivAt_globalCurve q s) t 0 ht h0

theorem globalCurve_add (q : E) (s t : ℝ) :
    D.globalCurve q (t+s)=D.globalCurve (D.globalCurve q s) t := by
  let γ : ℝ → E := fun u => D.globalCurve q (u+s)
  have hd (u : ℝ) : HasDerivAt γ (D.field (γ u)) u := by
    have h := HasDerivAt.scomp (h := fun v : ℝ => v+s) u (D.hasDerivAt_globalCurve q (u+s))
      ((hasDerivAt_id u).add_const s)
    simpa only [Function.comp_def,one_smul] using h
  exact eqOn_integralCurves_of_contDiffAt D.field γ (D.globalCurve (D.globalCurve q s)) univ
    isOpen_univ isPreconnected_univ (fun u _ => hd u)
    (fun u _ => D.hasDerivAt_globalCurve _ u) (fun _ _ => D.contDiff.contDiffAt)
    0 (mem_univ _) (by simp only [γ,zero_add,D.globalCurve_zero]) (mem_univ t)

theorem exists_global_integralCurve (q : E) :
    ∃ γ : ℝ → E, γ 0=q ∧ (∀ t : ℝ, HasDerivAt γ (D.field (γ t)) t) ∧
      ∀ t : ℝ, D.invariant (γ t)=D.invariant q :=
  ⟨D.globalCurve q,D.globalCurve_zero q,D.hasDerivAt_globalCurve q,D.globalCurve_conserved q⟩

end CompactInvariantVectorField
end NLS.FunctionalAnalysis
