import NLS.KdV.HillHminusDirichletSourcePhase
import NLS.ZakharovShabat.SourcePhaseCanonicalRoots
import NLS.ZakharovShabat.SourceAngularRootSheet

noncomputable section
set_option autoImplicit false
open Set Complex NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV

/-- The actual Hill sheet prescribed by a terminal multiplier value.
This retains that value before any cut or square-root sign is chosen. -/
def hillHminusPrescribedRoot (w : ℂ) (t : ℂ × PeriodOneHminusOne) : ℂ :=
  prescribedSquareRoot (fun t : ℂ × PeriodOneHminusOne => hillHminusRadicand t.2 t.1) w t

def hillHminusPrescribedRootDomain (w : ℂ) : Set (ℂ × PeriodOneHminusOne) :=
  prescribedSquareRootDomain (fun t : ℂ × PeriodOneHminusOne => hillHminusRadicand t.2 t.1) w

theorem analyticOnNhd_hillHminusPrescribedRoot (w : ℂ) :
    AnalyticOnNhd ℂ (hillHminusPrescribedRoot w) (hillHminusPrescribedRootDomain w) :=
  analyticOnNhd_prescribedSquareRoot _ _ analyticOnNhd_hillHminusRadicand_joint

theorem hillHminusPrescribedRoot_sq (w : ℂ) (hw : w≠0) (t : ℂ × PeriodOneHminusOne) :
    hillHminusPrescribedRoot w t^2=hillHminusRadicand t.2 t.1 :=
  prescribedSquareRoot_sq _ _ hw t

theorem hillHminusPrescribedRoot_ne_zero (w : ℂ) (hw : w≠0)
    (t : ℂ × PeriodOneHminusOne) (ht : t∈hillHminusPrescribedRootDomain w) :
    hillHminusPrescribedRoot w t≠0 :=
  prescribedSquareRoot_ne_zero _ _ hw t ht

/-- Agreement with the literal ORIGINAL physical radicand prescription,
including its sign and values on canonical cuts. -/
theorem hillHminusPrescribedRoot_original_source_agreement
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0) (w E : ℂ) :
    hillHminusPrescribedRoot w (E,hillOriginalHminusSource q)=
      prescribedSquareRoot (hillL2Radicand (SpectralWeight.one.toCoeff q)) w E := by
  unfold hillHminusPrescribedRoot prescribedSquareRoot
  dsimp only
  rw [hillHminusRadicand_original_source_agreement q hq]

namespace HillHminusPsiChart

/-- At every complex frequency the actual scalar radicand is exactly
the angular source radicand at the actual ordinary Dirichlet source. -/
theorem radicand_squared_frequency_eq_sourcePhase (P : HillHminusPsiChart)
    (a : PeriodOneHminusOne) (ha : a∈P.source) (z : ℂ) :
    hillHminusRadicand a (z^2-P.miura.energyShift)=
      sourceAngularRadicand (by simp) (z,P.dirichletSource a) := by
  rw [hillHminusRadicand,hillHminusDiscriminant_eq_chart P.miura a ha.1,
    HillHminusMiuraChart.trace,sub_add_cancel,
    hillMiuraL2Discriminant_square]
  change hillMiuraFrequencyTrace (P.miura.lift a) z^2-4=
    canonicalDiscriminant (by simp)
      (periodOnePotential (sourcePhase (hillMiuraDiagonal (P.miura.lift a)))) z^2-4
  rw [canonicalDiscriminant_eq_l2_source,l2Discriminant_sourcePhase,
    ← canonicalDiscriminant_eq_l2_source]
  rfl

/-- EXACT prescribed-sheet pullback. In particular a multiplier-normalized
energy sheet is the same source sheet, without an unresolved sign. -/
theorem prescribedRoot_squared_frequency_eq_sourcePhase (P : HillHminusPsiChart)
    (a : PeriodOneHminusOne) (ha : a∈P.source) (w z : ℂ) :
    hillHminusPrescribedRoot w (z^2-P.miura.energyShift,a)=
      sourceAngularRootSheet (by simp) w (z,P.dirichletSource a) := by
  unfold hillHminusPrescribedRoot sourceAngularRootSheet prescribedSquareRoot
  dsimp only
  rw [P.radicand_squared_frequency_eq_sourcePhase a ha z]

/-- The corresponding REGULAR sheet domains agree exactly as well. -/
theorem prescribedRoot_squared_frequency_domain_iff (P : HillHminusPsiChart)
    (a : PeriodOneHminusOne) (ha : a∈P.source) (w z : ℂ) :
    (z^2-P.miura.energyShift,a)∈hillHminusPrescribedRootDomain w ↔
      (z,P.dirichletSource a)∈sourceAngularRootSheetDomain (by simp) w := by
  change hillHminusRadicand a (z^2-P.miura.energyShift)/w^2∈slitPlane ↔
    sourceAngularRadicand (by simp) (z,P.dirichletSource a)/w^2∈slitPlane
  rw [P.radicand_squared_frequency_eq_sourcePhase a ha z]

/-- The same prescribed sheet at opposite frequencies has the SAME
value: its radicand is the scalar energy radicand, which is even. -/
theorem sourcePhase_prescribedRoot_neg (P : HillHminusPsiChart)
    (a : PeriodOneHminusOne) (ha : a∈P.source) (w z : ℂ) :
    sourceAngularRootSheet (by simp) w (-z,P.dirichletSource a)=
      sourceAngularRootSheet (by simp) w (z,P.dirichletSource a) := by
  rw [← P.prescribedRoot_squared_frequency_eq_sourcePhase a ha w (-z),
    ← P.prescribedRoot_squared_frequency_eq_sourcePhase a ha w z,neg_sq]

/-- The terminal prescription is the actual ORIGINAL sheet value,
not an arbitrary square root of the same radicand. -/
theorem prescribedRoot_dirichlet_base (P : HillHminusPsiChart) (n : ℕ+)
    (a : PeriodOneHminusOne) (ha : a∈P.source)
    (hz : P.dirichletFrequency (n:ℕ) a≠0) (hw : P.dirichletSheet n a≠0) :
    (P.dirichletEnergy n a,a)∈hillHminusPrescribedRootDomain (P.dirichletSheet n a) ∧
      hillHminusPrescribedRoot (P.dirichletSheet n a) (P.dirichletEnergy n a,a)=P.dirichletSheet n a := by
  have hnonzero : sourceAntiDiscriminantCandidate (by simp) (by norm_num)
      (P.dirichletSource a) (canonicalPeriodOneBoundaryRoots (by simp) (by norm_num)
        .dirichlet (P.dirichletSource a) (n:ℕ))≠0 := by
    change sourceBoundaryTerminalAntiDiscriminant (by simp) (by norm_num)
      .dirichlet (n:ℕ) (P.dirichletSource a)≠0
    rw [← P.dirichletSheet_eq_sourcePhase n a ha hz]
    exact hw
  have hs := sourceAngularRootSheet_dirichlet_base (by simp) (by norm_num)
    (P.dirichletSource a) (n:ℕ) hnonzero
  dsimp only at hs
  change (canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet
      (P.dirichletSource a) (n:ℕ),P.dirichletSource a)∈sourceAngularRootSheetDomain (by simp)
      (sourceBoundaryTerminalAntiDiscriminant (by simp) (by norm_num) .dirichlet (n:ℕ)
        (P.dirichletSource a)) ∧
    sourceAngularRootSheet (by simp) (sourceBoundaryTerminalAntiDiscriminant (by simp)
      (by norm_num) .dirichlet (n:ℕ) (P.dirichletSource a))
        (canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet
          (P.dirichletSource a) (n:ℕ),P.dirichletSource a)=
      sourceBoundaryTerminalAntiDiscriminant (by simp) (by norm_num) .dirichlet (n:ℕ)
        (P.dirichletSource a) at hs
  rw [← P.dirichletSheet_eq_sourcePhase n a ha hz,
    ← P.dirichletFrequency_eq_sourcePhase] at hs
  have he : P.dirichletEnergy n a=(P.dirichletFrequency (n:ℕ) a)^2-P.miura.energyShift := rfl
  rw [he,P.prescribedRoot_squared_frequency_domain_iff a ha,
    P.prescribedRoot_squared_frequency_eq_sourcePhase a ha]
  exact hs

end HillHminusPsiChart
end NLS.KdV
