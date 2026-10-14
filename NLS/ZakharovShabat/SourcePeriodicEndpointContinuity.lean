import NLS.ZakharovShabat.SourcePeriodicMidpointGapContinuity

/-!
# Original periodic endpoint continuity, in sequence norm

At every real-type source, both actual ordered endpoint displacements are
continuous in ℓp under arbitrary complex source perturbations. Consequently
one source neighborhood controls both endpoints at every signed index.
No simplicity or open-gap hypothesis is needed.
-/

noncomputable section
open Set Metric Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The left endpoint displacement is recovered exactly from the midpoint and gap. -/
theorem sourcePeriodicLeftDisplacement_eq_midpoint_sub_half_gap (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) :
    canonicalPeriodicLeftDisplacement hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) =
      sourcePeriodicMidpointDisplacement hp hp1 φ-(1/2 : ℂ) • sourcePeriodicGapDisplacement hp hp1 φ := by
  simp only [sourcePeriodicMidpointDisplacement,sourcePeriodicGapDisplacement]
  module

/-- The right endpoint displacement is recovered exactly from the midpoint and gap. -/
theorem sourcePeriodicRightDisplacement_eq_midpoint_add_half_gap (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) :
    canonicalPeriodicRightDisplacement hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) =
      sourcePeriodicMidpointDisplacement hp hp1 φ+(1/2 : ℂ) • sourcePeriodicGapDisplacement hp hp1 φ := by
  simp only [sourcePeriodicMidpointDisplacement,sourcePeriodicGapDisplacement]
  module

/-- Both original ordered endpoint displacement sequences are continuous at real type. -/
theorem continuousAt_sourcePeriodicEndpointDisplacements_of_realType (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ContinuousAt (fun ψ : CoeffPair p =>
      (canonicalPeriodicLeftDisplacement hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ),
        canonicalPeriodicRightDisplacement hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ))) φ := by
  have hm := continuousAt_sourcePeriodicMidpointDisplacement_of_realType hp hp1 φ hφ
  have hg := (continuousAt_sourcePeriodicGapDisplacement_of_realType hp hp1 φ hφ).const_smul (1/2 : ℂ)
  simpa only [sourcePeriodicLeftDisplacement_eq_midpoint_sub_half_gap,
    sourcePeriodicRightDisplacement_eq_midpoint_add_half_gap,Pi.sub_apply,Pi.add_apply,Pi.smul_apply] using (hm.sub hg).prodMk (hm.add hg)

/-- One original neighborhood controls both endpoints uniformly over all signed indices. -/
theorem exists_uniform_sourcePeriodicEndpoint_neighborhood (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧ ∀ ψ ∈ U, ∀ n : ℤ,
      ‖canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n-
        canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n‖ < ε ∧
      ‖canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n-
        canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n‖ < ε := by
  obtain ⟨δ,hδ,hd⟩ := Metric.continuousAt_iff.mp
    (continuousAt_sourcePeriodicEndpointDisplacements_of_realType hp hp1 φ hφ) ε hε
  refine ⟨ball φ δ,isOpen_ball,mem_ball_self hδ,?_⟩
  intro ψ hψ n
  have hb := hd hψ
  simp only [dist_eq_norm,Prod.norm_def,Prod.fst_sub,Prod.snd_sub,max_lt_iff] at hb
  have hp0 : p ≠ 0 := (zero_lt_one.trans hp1).ne'
  have hl := (lp.norm_apply_le_norm hp0
    (canonicalPeriodicLeftDisplacement hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ)-
      canonicalPeriodicLeftDisplacement hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ)) n).trans_lt hb.1
  have hr := (lp.norm_apply_le_norm hp0
    (canonicalPeriodicRightDisplacement hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ)-
      canonicalPeriodicRightDisplacement hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ)) n).trans_lt hb.2
  simp only [lp.coeFn_sub,Pi.sub_apply,canonicalPeriodicLeftDisplacement_apply,
    canonicalPeriodicRightDisplacement_apply,sub_sub_sub_cancel_right] at hl hr
  exact ⟨hl,hr⟩

end NLS.ZakharovShabat
