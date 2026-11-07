import NLS.KdV.HillL2OnIndexWeights
import NLS.ZakharovShabat.SourceH1DirichletGapHilbertMajorants

/-! The ACTUAL physical Hill gap and auxiliary-divisor midpoint
displacement have Hilbert majorants after ONE index derivative on
complex L2 neighborhoods. The SAME retained patch and source are used. -/
noncomputable section
open Set Complex Filter Topology NLS.ZakharovShabat
namespace NLS.KdV.HillProductEquationPatch

private theorem real_rotated_H1 (P : HillProductEquationPatch) (q : Coeff 2)
    (hq : periodOneL2Inclusion q ∈ P.source)
    (hr : IsRealPeriodOneHminusOne (periodOneL2Inclusion q)) :
    IsRealType (CoeffPair.toMax 2 (sobolevSourceInclusion (P.rotatedDiracL2Lift q))) := by
  rw [P.sobolevSourceInclusion_rotatedDiracL2Lift q hq]
  exact P.isRealType_rotatedDiracSource _ hq hr

private theorem eventually_rotated_in (P : HillProductEquationPatch) (q : Coeff 2)
    (hq : periodOneL2Inclusion q ∈ P.source) (V : Set (ScalarDomain 2 × ScalarDomain 2))
    (hV : IsOpen V) (hqV : P.rotatedDiracL2Lift q ∈ V) :
    ∀ᶠ r in 𝓝 q, P.rotatedDiracL2Lift r ∈ V :=
  (P.analytic_rotatedDiracL2Lift q hq).continuousAt.tendsto.eventually (hV.mem_nhds hqV)

private theorem transfer_majorants (P : HillProductEquationPatch) (r : Coeff 2)
    (hrP : periodOneL2Inclusion r ∈ P.source) (G D : Coeff 2)
    (hb : ∀ n : ℕ+, (1+(n:ℝ))*(
      ‖sourcePeriodicGapDisplacement (by simp) (by norm_num) (sobolevSourceInclusion (P.rotatedDiracL2Lift r)) ((n:ℕ):ℤ)‖+
      ‖sourceDirichletMidpointDisplacement (by simp) (by norm_num) (sobolevSourceInclusion (P.rotatedDiracL2Lift r)) ((n:ℕ):ℤ)‖) ≤
        ‖G ((n:ℕ):ℤ)‖+‖D ((n:ℕ):ℤ)‖) (n : ℕ+) :
    (1+(n:ℝ))*(‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num)
      (P.sourcePsi (periodOneL2Inclusion r)) ((n:ℕ):ℤ)‖+
        ‖P.physicalAbelianMidpointDisplacement (periodOneL2Inclusion r) ((n:ℕ):ℤ)‖) ≤
          ‖G ((n:ℕ):ℤ)‖+‖D ((n:ℕ):ℤ)‖ := by
  have h := hb n
  rw [P.sobolevSourceInclusion_rotatedDiracL2Lift r hrP,
    P.sourcePeriodicGapDisplacement_rotated,← P.physicalAbelianMidpointDisplacement_eq_rotated] at h
  exact h

theorem exists_local_l2Abelian_Hilbert_weight_majorants (P : HillProductEquationPatch)
    (q : Coeff 2) (hq : periodOneL2Inclusion q ∈ P.source)
    (hr : IsRealPeriodOneHminusOne (periodOneL2Inclusion q)) :
    ∃ U : Set (Coeff 2), IsOpen U ∧ q ∈ U ∧ (∀ r ∈ U, periodOneL2Inclusion r ∈ P.source) ∧
      ∃ M : ℝ, 0 ≤ M ∧ ∀ r ∈ U, ∃ G D : Coeff 2, ‖G‖+‖D‖ ≤ M ∧ ∀ n : ℕ+,
        (1+(n:ℝ))*(‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num)
            (P.sourcePsi (periodOneL2Inclusion r)) ((n:ℕ):ℤ)‖+
          ‖P.physicalAbelianMidpointDisplacement (periodOneL2Inclusion r) ((n:ℕ):ℤ)‖) ≤
            ‖G ((n:ℕ):ℤ)‖+‖D ((n:ℕ):ℤ)‖ := by
  obtain ⟨V,hV,hqV,M,hM,hmajor⟩ := exists_local_sourceH1Dirichlet_gap_Hilbert_majorants
    ⟨P.rotatedDiracL2Lift q,P.real_rotated_H1 q hq hr⟩
  have hsource : ∀ᶠ r in 𝓝 q, periodOneL2Inclusion r ∈ P.source :=
    periodOneL2Inclusion.continuous.continuousAt.tendsto.eventually (P.source_open.mem_nhds hq)
  have hall : ∀ᶠ r in 𝓝 q, periodOneL2Inclusion r ∈ P.source ∧ ∃ G D : Coeff 2, ‖G‖+‖D‖ ≤ M ∧
      ∀ n : ℕ+, (1+(n:ℝ))*(‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num)
        (P.sourcePsi (periodOneL2Inclusion r)) ((n:ℕ):ℤ)‖+
          ‖P.physicalAbelianMidpointDisplacement (periodOneL2Inclusion r) ((n:ℕ):ℤ)‖) ≤
            ‖G ((n:ℕ):ℤ)‖+‖D ((n:ℕ):ℤ)‖ :=
    (hsource.and (P.eventually_rotated_in q hq V hV hqV)).mono (fun r h => by
      obtain ⟨G,D,hGD,hb⟩ := hmajor _ h.2
      exact ⟨h.1,G,D,hGD,P.transfer_majorants r h.1 G D hb⟩)
  obtain ⟨U,hUsub,hU,hqU⟩ := _root_.mem_nhds_iff.mp hall
  exact ⟨U,hU,hqU,fun r hrU => (hUsub hrU).1,M,hM,fun r hrU => (hUsub hrU).2⟩

end NLS.KdV.HillProductEquationPatch
