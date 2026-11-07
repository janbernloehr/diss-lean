import NLS.MKdV.QuasiHillL2BoundaryJets
import NLS.KdV.SingularDirichletForcedStateRealization
import NLS.KdV.SingularDirichletChains
import NLS.FunctionalAnalysis.PencilChainEquations

/-! # Actual original complex Dirichlet state jets and native chain reconstruction

The actual shifted Miura chart supplies the rough normalized IVP. Its
terminal scalar jets are those of the original normalized characteristic.
Every scalar Taylor-kernel vector reconstructs to an actual full-domain
native chain; every scalar position agrees on the whole closed interval.
-/
noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra NLS.FunctionalAnalysis NLS.ComplexAnalysis
namespace NLS.KdV
open NLS.Fourier NLS.MKdV NLS.ZakharovShabat

/-- Full uniform state jets at the actual original complex H-minus-one source. -/
def hillHminusDirichletStateJet (q : PeriodOneHminusOne) (lambda : ℂ) (N : ℕ) :
    (Fin N → ℂ) →ₗ[ℂ] (Fin N → Curve (ℂ × ℂ)) :=
  quasiHillDirichletAmplitudeJet ((hillHminusMiuraChartAt q).lift q)
    (lambda+(hillHminusMiuraChartAt q).energyShift) N

theorem hillHminusDirichletStateJet_initial (q : PeriodOneHminusOne) (lambda : ℂ)
    (N : ℕ) (a : Fin N → ℂ) (k : Fin N) :
    hillHminusDirichletStateJet q lambda N a k ⟨0,by constructor <;> norm_num⟩ = (0,a k) :=
  quasiHillDirichletAmplitudeJet_initial _ _ N a k

theorem hillHminusDirichletStateJet_intervalH1 (q : PeriodOneHminusOne) (lambda : ℂ)
    (N : ℕ) (a : Fin N → ℂ) (k : Fin N) :
    HasIntervalH1Regularity (fun x => (extend (hillHminusDirichletStateJet q lambda N a k) x).1) ∧
    HasIntervalH1Regularity (fun x => (extend (hillHminusDirichletStateJet q lambda N a k) x).2) :=
  quasiHillDirichletAmplitudeJet_intervalH1 _ _ N a k

/-- The terminal state jets use the ORIGINAL characteristic and energy, with
the constant Miura shift canceled before taking Taylor coefficients. -/
theorem hillHminusDirichletStateJet_terminal (q : PeriodOneHminusOne) (lambda : ℂ)
    (p : FormalMultilinearSeries ℂ ℂ ℂ)
    (hp : HasFPowerSeriesAt (fun t : ℂ => hillHminusDirichlet q (lambda+t)) p 0)
    (N : ℕ) (a : Fin N → ℂ) :
    (fun k : Fin N => (hillHminusDirichletStateJet q lambda N a k
      ⟨1,by constructor <;> norm_num⟩).1) = scalarTaylorJetMap (scalarFormalTaylor p) N a := by
  let C := hillHminusMiuraChartAt q
  have he : (fun t : ℂ => quasiHillL2Dirichlet (C.lift q) ((lambda+C.energyShift)+t)) =
      fun t : ℂ => hillHminusDirichlet q (lambda+t) := by
    funext t
    rw [hillHminusDirichlet_eq_miura_of_shifted_image q (C.lift q) C.energyShift (lambda+t)
      (C.image q (mem_hillHminusMiuraChartAt q))]
    congr 1
    ring
  have hp' : HasFPowerSeriesAt
      (fun t : ℂ => quasiHillL2Dirichlet (C.lift q) ((lambda+C.energyShift)+t)) p 0 := by
    rw [he]
    exact hp
  exact quasiHillDirichletAmplitudeJet_terminal (C.lift q) (lambda+C.energyShift) p hp' N a

/-- Exact original scalar Taylor-kernel criterion for the actual state endpoint jets. -/
theorem mem_scalarTaylorKernel_iff_hillHminusDirichletStateJet_terminal_zero
    (q : PeriodOneHminusOne) (lambda : ℂ) (p : FormalMultilinearSeries ℂ ℂ ℂ)
    (hp : HasFPowerSeriesAt (fun t : ℂ => hillHminusDirichlet q (lambda+t)) p 0)
    (N : ℕ) (a : Fin N → ℂ) :
    a ∈ LinearMap.ker (scalarTaylorJetMap (scalarFormalTaylor p) N) ↔
      ∀ k : Fin N, (hillHminusDirichletStateJet q lambda N a k
        ⟨1,by constructor <;> norm_num⟩).1 = 0 := by
  rw [LinearMap.mem_ker, ← hillHminusDirichletStateJet_terminal q lambda p hp N a]
  exact funext_iff

/-- The first actual source state coefficient is a genuine homogeneous physical state. -/
theorem isQuasiHillL2ForcedSolution_hillHminusStateJet_zero (q : PeriodOneHminusOne) (lambda : ℂ)
    (N : ℕ) (a : Fin N → ℂ) (hN : 0 < N) :
    IsQuasiHillL2ForcedSolution ((hillHminusMiuraChartAt q).lift q)
      (lambda+(hillHminusMiuraChartAt q).energyShift) 0
      (hillHminusDirichletStateJet q lambda N a ⟨0,hN⟩) :=
  isQuasiHillL2ForcedSolution_amplitudeCoefficient_zero _ _ N a hN

/-- Every later actual source state coefficient has precisely the preceding physical forcing. -/
theorem isQuasiHillL2ForcedSolution_hillHminusStateJet_succ (q : PeriodOneHminusOne) (lambda : ℂ)
    (N : ℕ) (a : Fin N → ℂ) (k : ℕ) (hk : k+1 < N) :
    IsQuasiHillL2ForcedSolution ((hillHminusMiuraChartAt q).lift q)
      (lambda+(hillHminusMiuraChartAt q).energyShift)
      (hillHminusDirichletStateJet q lambda N a ⟨k,Nat.lt_trans (Nat.lt_succ_self k) hk⟩)
      (hillHminusDirichletStateJet q lambda N a ⟨k+1,hk⟩) :=
  isQuasiHillL2ForcedSolution_amplitudeCoefficient_succ _ _ N a k hk

/-- Each scalar Taylor-kernel coefficient has a UNIQUE native H1 representative,
with its actual scalar position retained on the entire original closed interval. -/
theorem existsUnique_native_of_hillHminusDirichletStateJet
    (q : PeriodOneHminusOne) (lambda : ℂ) (p : FormalMultilinearSeries ℂ ℂ ℂ)
    (hp : HasFPowerSeriesAt (fun t : ℂ => hillHminusDirichlet q (lambda+t)) p 0)
    (N : ℕ) (a : Fin N → ℂ) (ha : a ∈ LinearMap.ker (scalarTaylorJetMap (scalarFormalTaylor p) N))
    (k : Fin N) :
    ∃! f : UnitDirichletH1, ∀ x ∈ Icc (0:ℝ) 1, unitDirichletRepresentative f x =
      (extend (hillHminusDirichletStateJet q lambda N a k) x).1 := by
  apply existsUnique_unitDirichletRepresentative _ (hillHminusDirichletStateJet_intervalH1 q lambda N a k).1
  · rw [extend_coe _ (⟨0,by constructor <;> norm_num⟩ : Icc (0:ℝ) 1),
      hillHminusDirichletStateJet_initial]
  · rw [extend_coe _ (⟨1,by constructor <;> norm_num⟩ : Icc (0:ℝ) 1)]
    exact (mem_scalarTaylorKernel_iff_hillHminusDirichletStateJet_terminal_zero q lambda p hp N a).mp ha k

/-- EVERY original scalar characteristic Taylor-kernel vector reconstructs
to an ACTUAL full native Dirichlet chain, with no formal domain relaxation. -/
theorem exists_native_chain_of_scalarTaylorKernel
    (q : PeriodOneHminusOne) (lambda : ℂ) (p : FormalMultilinearSeries ℂ ℂ ℂ)
    (hp : HasFPowerSeriesAt (fun t : ℂ => hillHminusDirichlet q (lambda+t)) p 0)
    (N : ℕ) (a : Fin N → ℂ) (ha : a ∈ LinearMap.ker (scalarTaylorJetMap (scalarFormalTaylor p) N)) :
    ∃ v : singularDirichletChainSpace (periodOneOriginal q) lambda N,
      ∀ (k : Fin N) (x : ℝ), x ∈ Icc (0:ℝ) 1 → unitDirichletRepresentative (v.val k) x =
        (extend (hillHminusDirichletStateJet q lambda N a k) x).1 := by
  choose v hv using fun k => (existsUnique_native_of_hillHminusDirichletStateJet q lambda p hp N a ha k).exists
  have hchain : v ∈ singularDirichletChainSpace (periodOneOriginal q) lambda N := by
    apply (mem_pencilChainSpace_iff_equations singularDirichletDomainInclusion.toLinearMap
      (singularDirichletOperator (periodOneOriginal q)-lambda • singularDirichletDomainInclusion).toLinearMap N v).mpr
    constructor
    · intro hN
      have h := singularDirichlet_source_forced_of_state q lambda 0
        (hillHminusDirichletStateJet q lambda N a ⟨0,hN⟩)
        (isQuasiHillL2ForcedSolution_hillHminusStateJet_zero q lambda N a hN) (v ⟨0,hN⟩) 0
        (fun x hx => (hv ⟨0,hN⟩ x hx).symm) (fun x _ => by
          change (0:ℂ) = periodOneSobolevSynthesis (0 : ScalarDomain 2) (x : AddCircle (2:ℝ))
          rw [map_zero]
          rfl)
      rw [map_zero] at h
      exact h
    · intro k hk
      exact singularDirichlet_source_forced_of_state q lambda _ _
        (isQuasiHillL2ForcedSolution_hillHminusStateJet_succ q lambda N a k hk) _ _
        (fun x hx => (hv ⟨k+1,hk⟩ x hx).symm)
        (fun x hx => (hv ⟨k,Nat.lt_trans (Nat.lt_succ_self k) hk⟩ x hx).symm)
  exact ⟨⟨v,hchain⟩,hv⟩

/-- The actual full native chain reconstructed from a scalar Taylor-kernel
vector is unique when its original scalar positions are retained. -/
theorem existsUnique_native_chain_of_scalarTaylorKernel
    (q : PeriodOneHminusOne) (lambda : ℂ) (p : FormalMultilinearSeries ℂ ℂ ℂ)
    (hp : HasFPowerSeriesAt (fun t : ℂ => hillHminusDirichlet q (lambda+t)) p 0)
    (N : ℕ) (a : Fin N → ℂ) (ha : a ∈ LinearMap.ker (scalarTaylorJetMap (scalarFormalTaylor p) N)) :
    ∃! v : singularDirichletChainSpace (periodOneOriginal q) lambda N,
      ∀ (k : Fin N) (x : ℝ), x ∈ Icc (0:ℝ) 1 → unitDirichletRepresentative (v.val k) x =
        (extend (hillHminusDirichletStateJet q lambda N a k) x).1 := by
  obtain ⟨v,hv⟩ := exists_native_chain_of_scalarTaylorKernel q lambda p hp N a ha
  refine ⟨v,hv,?_⟩
  intro w hw
  apply Subtype.ext
  funext k
  apply unitDirichletRepresentative_injective_on_interval
  intro x hx
  exact (hw k x hx).trans (hv k x hx).symm

end NLS.KdV
