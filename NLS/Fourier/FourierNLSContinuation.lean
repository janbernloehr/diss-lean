import NLS.Fourier.UniformLocalNLS
import NLS.FunctionalAnalysis.ClosedIntegralCurveJoin

/-! # Continuation of bounded Fourier NLS trajectories

Matching trajectories glue on adjacent closed intervals. A bound at an
endpoint gives an explicit uniform extension length. A trajectory bounded
up to a finite open endpoint therefore extends beyond that endpoint.
-/
noncomputable section
open Set
open NLS.FunctionalAnalysis
namespace NLS.Fourier

/-- Matching Fourier trajectories glue with the equation valid at the join. -/
theorem IsFourierNLSTrajectoryOn.join
    {w : SpectralWeight} {a c b : ℝ} {u v : ℝ → WeightedCoeff w.toWeight 1}
    (hu : IsFourierNLSTrajectoryOn w a c u) (hv : IsFourierNLSTrajectoryOn w c b v)
    (hac : a ≤ c) (hcb : c ≤ b) (he : u c = v c) :
    IsFourierNLSTrajectoryOn w a b (joinClosedCurves c u v) := by
  have hd := hasDerivWithinAt_joinClosedCurves (nlsInteraction w)
    (nlsToInteraction w u) (nlsToInteraction w v) a c b hac hcb
    hu.hasDerivWithinAt_interaction hv.hasDerivWithinAt_interaction
    (congrArg (nlsFreeFlow w.toWeight (-c)) he)
  have h := isFourierNLSTrajectoryOn_of_interaction w a b _ hd
  have heq : (fun time => nlsFreeFlow w.toWeight time
      (joinClosedCurves c (nlsToInteraction w u) (nlsToInteraction w v) time)) =
      joinClosedCurves c u v := by
    funext time
    by_cases ht : time ≤ c <;> simp only [joinClosedCurves,ht,ite_true,ite_false,nlsFreeFlow_nlsToInteraction]
  rwa [heq] at h

/-- A bounded right endpoint gives a uniform extension preserving the whole old interval. -/
theorem IsFourierNLSTrajectoryOn.extend_right
    {w : SpectralWeight} {a b : ℝ} {u : ℝ → WeightedCoeff w.toWeight 1}
    (hu : IsFourierNLSTrajectoryOn w a b u) (hab : a ≤ b)
    (B : ℝ) (hB : 0 ≤ B) (hb : ‖u b‖ ≤ B) :
    ∃ z : ℝ → WeightedCoeff w.toWeight 1,
      IsFourierNLSTrajectoryOn w a (b+nlsLocalTime B) z ∧ EqOn z u (Icc a b) := by
  have hT := nlsLocalTime_pos B hB
  obtain ⟨v,hv0,hv⟩ := exists_fourierNLS_on_uniform_interval w B hB b (u b) hb
  refine ⟨joinClosedCurves b u v,
    hu.join (hv.restrict (by linarith) le_rfl) hab (by linarith) hv0.symm,?_⟩
  intro time ht
  exact joinClosedCurves_of_le b u v ht.2

/-- The same extension length works backwards from a bounded left endpoint. -/
theorem IsFourierNLSTrajectoryOn.extend_left
    {w : SpectralWeight} {a b : ℝ} {u : ℝ → WeightedCoeff w.toWeight 1}
    (hu : IsFourierNLSTrajectoryOn w a b u) (hab : a ≤ b)
    (B : ℝ) (hB : 0 ≤ B) (ha : ‖u a‖ ≤ B) :
    ∃ z : ℝ → WeightedCoeff w.toWeight 1,
      IsFourierNLSTrajectoryOn w (a-nlsLocalTime B) b z ∧ EqOn z u (Icc a b) := by
  have hT := nlsLocalTime_pos B hB
  obtain ⟨v,hv0,hv⟩ := exists_fourierNLS_on_uniform_interval w B hB a (u a) ha
  refine ⟨joinClosedCurves a v u,
    (hv.restrict le_rfl (by linarith)).join hu (by linarith) hab hv0,?_⟩
  intro time ht
  exact joinClosedCurves_of_ge a v u hv0 ht.1

/-- A bounded trajectory on all closed truncations of `[a,b)` extends past `b`.
No endpoint value or limit at `b` is assumed; the extension preserves every
old value strictly before that endpoint. -/
theorem exists_fourierNLS_extension_of_bounded_Ico
    (w : SpectralWeight) (a b : ℝ) (hab : a < b)
    (u : ℝ → WeightedCoeff w.toWeight 1)
    (hu : ∀ c ∈ Ico a b, IsFourierNLSTrajectoryOn w a c u)
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ r ∈ Ico a b, ‖u r‖ ≤ B) :
    ∃ d > b, ∃ z : ℝ → WeightedCoeff w.toWeight 1,
      IsFourierNLSTrajectoryOn w a d z ∧ EqOn z u (Ico a b) := by
  let c := max a (b-nlsLocalTime B/2)
  have hT := nlsLocalTime_pos B hB
  have hac : a ≤ c := le_max_left _ _
  have hcb : c < b := max_lt hab (by linarith)
  have hbc : b < c+nlsLocalTime B := by
    have hc : b-nlsLocalTime B/2 ≤ c := le_max_right _ _
    linarith
  obtain ⟨z,hz,he⟩ := (hu c ⟨hac,hcb⟩).extend_right hac B hB (hbound c ⟨hac,hcb⟩)
  refine ⟨c+nlsLocalTime B,hbc,z,hz,?_⟩
  intro time ht
  have hzt := hz.restrict le_rfl (ht.2.le.trans hbc.le)
  exact (hzt.eqOn_of_eq_at_closed (hu time ht) a ⟨le_rfl,ht.1⟩
    (he ⟨le_rfl,hac⟩)) ⟨ht.1,le_rfl⟩

/-- The corresponding backward continuation criterion on `(a,b]`. -/
theorem exists_fourierNLS_extension_of_bounded_Ioc
    (w : SpectralWeight) (a b : ℝ) (hab : a < b)
    (u : ℝ → WeightedCoeff w.toWeight 1)
    (hu : ∀ c ∈ Ioc a b, IsFourierNLSTrajectoryOn w c b u)
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ r ∈ Ioc a b, ‖u r‖ ≤ B) :
    ∃ d < a, ∃ z : ℝ → WeightedCoeff w.toWeight 1,
      IsFourierNLSTrajectoryOn w d b z ∧ EqOn z u (Ioc a b) := by
  let c := min b (a+nlsLocalTime B/2)
  have hT := nlsLocalTime_pos B hB
  have hcb : c ≤ b := min_le_left _ _
  have hac : a < c := lt_min hab (by linarith)
  have hca : c-nlsLocalTime B < a := by
    have hc : c ≤ a+nlsLocalTime B/2 := min_le_right _ _
    linarith
  obtain ⟨z,hz,he⟩ := (hu c ⟨hac,hcb⟩).extend_left hcb B hB (hbound c ⟨hac,hcb⟩)
  refine ⟨c-nlsLocalTime B,hca,z,hz,?_⟩
  intro time ht
  have hzt := hz.restrict (hca.le.trans ht.1.le) le_rfl
  exact (hzt.eqOn_of_eq_at_closed (hu time ht) b ⟨ht.2,le_rfl⟩
    (he ⟨hcb,le_rfl⟩)) ⟨le_rfl,ht.2⟩

end NLS.Fourier
