import NLS.KdV.SingularDirichletChainStates

/-! # Reverse reconstruction of every actual native Dirichlet chain

Actual physical coefficient states give the initial quasi-derivative
amplitudes. Forced IVP uniqueness identifies every coefficient with the
normalized rough IVP Taylor state. Its actual terminal positions vanish,
so these amplitudes lie in the ORIGINAL characteristic Taylor kernel.
-/
noncomputable section
open Set Complex NLS.LinearVolterra NLS.FunctionalAnalysis NLS.ComplexAnalysis
namespace NLS.KdV
open NLS.Fourier NLS.MKdV

theorem hillHminusDirichletStateJet_injective (q : PeriodOneHminusOne) (lambda : ℂ) (N : ℕ) :
    Function.Injective (hillHminusDirichletStateJet q lambda N) :=
  quasiHillDirichletAmplitudeJet_injective _ _ N

/-- Every actual source Taylor coefficient has a genuine forced physical state equation. -/
theorem exists_preceding_hillHminusDirichletStateJet (q : PeriodOneHminusOne) (lambda : ℂ)
    (N : ℕ) (a : Fin N → ℂ) (k : Fin N) :
    ∃ v : Curve (ℂ × ℂ), IsQuasiHillL2ForcedSolution ((hillHminusMiuraChartAt q).lift q)
      (lambda+(hillHminusMiuraChartAt q).energyShift) v (hillHminusDirichletStateJet q lambda N a k) := by
  obtain ⟨n,hn⟩ := k
  cases n with
  | zero => exact ⟨0,isQuasiHillL2ForcedSolution_hillHminusStateJet_zero q lambda N a hn⟩
  | succ n => exact ⟨_,isQuasiHillL2ForcedSolution_hillHminusStateJet_succ q lambda N a n hn⟩

/-- All scalar positions determine the ENTIRE amplitude vector, using the
actual first physical row rather than a presumed boundary normalization. -/
theorem hillHminusDirichletStateJet_positions_injective (q : PeriodOneHminusOne)
    (lambda : ℂ) (N : ℕ) (a b : Fin N → ℂ)
    (hp : ∀ (k : Fin N) (t : Icc (0:ℝ) 1),
      (hillHminusDirichletStateJet q lambda N a k t).1 =
        (hillHminusDirichletStateJet q lambda N b k t).1) : a = b := by
  apply hillHminusDirichletStateJet_injective q lambda N
  funext k
  obtain ⟨v,hv⟩ := exists_preceding_hillHminusDirichletStateJet q lambda N a k
  obtain ⟨w,hw⟩ := exists_preceding_hillHminusDirichletStateJet q lambda N b k
  exact IsQuasiHillL2ForcedSolution.eq_of_position_eq _ _ v _ w _ hv hw (hp k)

/-- EVERY actual full-domain native chain comes from a scalar amplitude
vector in the ORIGINAL characteristic Taylor kernel, with all physical
positions identical on the full closed interval. -/
theorem exists_scalarTaylorKernel_of_native_chain
    (q : PeriodOneHminusOne) (lambda : ℂ) (p : FormalMultilinearSeries ℂ ℂ ℂ)
    (hp : HasFPowerSeriesAt (fun t : ℂ => hillHminusDirichlet q (lambda+t)) p 0)
    (N : ℕ) (v : singularDirichletChainSpace (periodOneOriginal q) lambda N) :
    ∃ a : Fin N → ℂ, a ∈ LinearMap.ker (scalarTaylorJetMap (scalarFormalTaylor p) N) ∧
      ∀ (k : Fin N) (x : ℝ), x ∈ Icc (0:ℝ) 1 → unitDirichletRepresentative (v.val k) x =
        (extend (hillHminusDirichletStateJet q lambda N a k) x).1 := by
  obtain ⟨w,hpos,hw0,hwnext⟩ := exists_physical_states_of_native_chain q lambda N v
  let a : Fin N → ℂ := fun k => (w k ⟨0,by constructor <;> norm_num⟩).2
  have hwi (k : Fin N) : w k ⟨0,by constructor <;> norm_num⟩ = (0,a k) := by
    apply Prod.ext
    · rw [hpos]
      exact unitDirichletRepresentative_zero (v.val k)
    · rfl
  have hmatch : ∀ (n : ℕ) (hn : n < N), hillHminusDirichletStateJet q lambda N a ⟨n,hn⟩ = w ⟨n,hn⟩ := by
    intro n
    induction n with
    | zero =>
      intro hn
      apply IsQuasiHillL2ForcedSolution.eq_of_initial_eq _ _ 0 _ _
        (isQuasiHillL2ForcedSolution_hillHminusStateJet_zero q lambda N a hn) (hw0 hn)
      rw [hillHminusDirichletStateJet_initial,hwi]
    | succ n ih =>
      intro hn
      have hprev := ih (Nat.lt_trans (Nat.lt_succ_self n) hn)
      have hstate := isQuasiHillL2ForcedSolution_hillHminusStateJet_succ q lambda N a n hn
      rw [hprev] at hstate
      apply IsQuasiHillL2ForcedSolution.eq_of_initial_eq _ _ _ _ _ hstate (hwnext n hn)
      rw [hillHminusDirichletStateJet_initial,hwi]
  have hm (k : Fin N) : hillHminusDirichletStateJet q lambda N a k = w k := hmatch k.val k.isLt
  refine ⟨a,?_,?_⟩
  · apply (mem_scalarTaylorKernel_iff_hillHminusDirichletStateJet_terminal_zero q lambda p hp N a).mpr
    intro k
    rw [hm k,hpos]
    exact unitDirichletRepresentative_one (v.val k)
  · intro k x hx
    rw [extend_coe _ ⟨x,hx⟩,hm k]
    exact (hpos k ⟨x,hx⟩).symm

/-- The scalar amplitude vector of every actual native chain is UNIQUE. -/
theorem existsUnique_scalarTaylorKernel_of_native_chain
    (q : PeriodOneHminusOne) (lambda : ℂ) (p : FormalMultilinearSeries ℂ ℂ ℂ)
    (hp : HasFPowerSeriesAt (fun t : ℂ => hillHminusDirichlet q (lambda+t)) p 0)
    (N : ℕ) (v : singularDirichletChainSpace (periodOneOriginal q) lambda N) :
    ∃! a : Fin N → ℂ, a ∈ LinearMap.ker (scalarTaylorJetMap (scalarFormalTaylor p) N) ∧
      ∀ (k : Fin N) (x : ℝ), x ∈ Icc (0:ℝ) 1 → unitDirichletRepresentative (v.val k) x =
        (extend (hillHminusDirichletStateJet q lambda N a k) x).1 := by
  obtain ⟨a,ha,hpos⟩ := exists_scalarTaylorKernel_of_native_chain q lambda p hp N v
  refine ⟨a,⟨ha,hpos⟩,?_⟩
  intro b hb
  apply hillHminusDirichletStateJet_positions_injective q lambda N b a
  intro k t
  have h1 := hb.2 k t.val t.property
  have h2 := hpos k t.val t.property
  rw [extend_coe _ t] at h1 h2
  exact h1.symm.trans h2

end NLS.KdV
