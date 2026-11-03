import NLS.KdV.HminusOneDirichletStateJets
import NLS.FunctionalAnalysis.PencilChainPrevious
import NLS.MKdV.QuasiHillL2ForcedStateUniqueness

/-! # Actual physical states of every native complex Dirichlet chain

Each native inhomogeneous equation supplies one actual continuous state.
Its scalar position is the unchanged original native representative. Only
the preceding scalar position enters its forcing, so all coefficient states
can be chosen together without circular initial-data assumptions.
-/
noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra NLS.FunctionalAnalysis
namespace NLS.KdV
open NLS.Fourier NLS.MKdV NLS.ZakharovShabat

/-- Every native forced equation has an actual physical state valid with
ANY preceding state representing its actual preceding native position. -/
theorem exists_physical_state_of_native_forced (q : PeriodOneHminusOne) (lambda : ℂ)
    (f g : UnitDirichletH1)
    (he : singularDirichletOperator (periodOneOriginal q) f-
      lambda • singularDirichletDomainInclusion f = singularDirichletDomainInclusion g) :
    ∃ w : Curve (ℂ × ℂ),
      (∀ t : Icc (0:ℝ) 1, (w t).1 = unitDirichletRepresentative f t.val) ∧
      ∀ v : Curve (ℂ × ℂ),
        (∀ t : Icc (0:ℝ) 1, (v t).1 = unitDirichletRepresentative g t.val) →
        IsQuasiHillL2ForcedSolution ((hillHminusMiuraChartAt q).lift q)
          (lambda+(hillHminusMiuraChartAt q).energyShift) v w := by
  obtain ⟨G,hGc,hGa,_hGr,hYd,hGd⟩ :=
    (singularDirichlet_source_forced_iff_physical_rows q lambda f g).mp he
  have hYc : Continuous (unitDirichletRepresentative f) := continuous_periodOneSobolevSynthesis f.val
  let w := quasiHillIntervalState (unitDirichletRepresentative f) G hYc hGc
  refine ⟨w,fun _ => rfl,?_⟩
  intro v hv
  apply isQuasiHillL2ForcedSolution_intervalState _ _ v (unitDirichletRepresentative f) G
    hYc hGc (absolutelyContinuous_unitDirichletRepresentative f) hGa hYd
  filter_upwards [hGd,ae_restrict_mem measurableSet_Ioc] with x hx hxi
  have hi : x ∈ Icc (0:ℝ) 1 := ⟨hxi.1.le,hxi.2⟩
  rw [extend_coe v ⟨x,hi⟩,hv ⟨x,hi⟩]
  exact hx

/-- Every ACTUAL native full-domain chain has actual physical coefficient
states with the exact homogeneous first step and every forced later step. -/
theorem exists_physical_states_of_native_chain (q : PeriodOneHminusOne) (lambda : ℂ)
    (N : ℕ) (v : singularDirichletChainSpace (periodOneOriginal q) lambda N) :
    ∃ w : Fin N → Curve (ℂ × ℂ),
      (∀ (k : Fin N) (t : Icc (0:ℝ) 1), (w k t).1 = unitDirichletRepresentative (v.val k) t.val) ∧
      (∀ hN : 0 < N, IsQuasiHillL2ForcedSolution ((hillHminusMiuraChartAt q).lift q)
        (lambda+(hillHminusMiuraChartAt q).energyShift) 0 (w ⟨0,hN⟩)) ∧
      ∀ (k : ℕ) (hk : k+1 < N),
        IsQuasiHillL2ForcedSolution ((hillHminusMiuraChartAt q).lift q)
          (lambda+(hillHminusMiuraChartAt q).energyShift)
          (w ⟨k,Nat.lt_trans (Nat.lt_succ_self k) hk⟩) (w ⟨k+1,hk⟩) := by
  have he (k : Fin N) : singularDirichletOperator (periodOneOriginal q) (v.val k)-
      lambda • singularDirichletDomainInclusion (v.val k) =
        singularDirichletDomainInclusion (pencilChainPrevious v.val k) :=
    (mem_pencilChainSpace_iff_previous singularDirichletDomainInclusion.toLinearMap
      (singularDirichletOperator (periodOneOriginal q)-lambda • singularDirichletDomainInclusion).toLinearMap N v.val).mp
        v.property k
  choose w hpos hforced using fun k => exists_physical_state_of_native_forced q lambda
    (v.val k) (pencilChainPrevious v.val k) (he k)
  refine ⟨w,hpos,?_,?_⟩
  · intro hN
    apply hforced ⟨0,hN⟩ 0
    intro t
    rw [pencilChainPrevious_zero]
    change (0:ℂ) = periodOneSobolevSynthesis (0 : ScalarDomain 2) (t.val : AddCircle (2:ℝ))
    rw [map_zero]
    rfl
  · intro k hk
    apply hforced ⟨k+1,hk⟩ (w ⟨k,Nat.lt_trans (Nat.lt_succ_self k) hk⟩)
    intro t
    rw [pencilChainPrevious_succ]
    exact hpos _ t

end NLS.KdV
