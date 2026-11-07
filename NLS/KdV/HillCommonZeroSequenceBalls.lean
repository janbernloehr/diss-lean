import NLS.KdV.HillCommonActualZeroSequences

/-! Real-centered full-l2 zero sequence charts use ONE domain before ALL
numerator indices. Native real-form identity gives whole complex overlap
agreement coordinate by coordinate, hence in the full Banach space. -/
noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal Classical
namespace NLS.KdV

structure HillHminusZeroSequenceBall where
  center : PeriodOneHminusOne
  center_real : IsRealPeriodOneHminusOne center
  radius : ℝ
  radius_pos : 0 < radius
  subset : ball center radius ⊆ hillHminusCanonicalPsiDomain
  value : ℕ+ → PeriodOneHminusOne → lp (fun _ : ℕ+ => ℂ) 2
  analytic_value : ∀ n, AnalyticOnNhd ℂ (value n) (ball center radius)
  real_eq : ∀ n q, q ∈ ball center radius → ∀ hq : IsRealPeriodOneHminusOne q,
    value n q = hillHminusPsiZeroDisplacement n ⟨q,hq⟩
  root : ∀ n m : ℕ+, m ≠ n → ∀ q ∈ ball center radius,
    hillHminusCanonicalPsi n (hillEnergySequenceZero m (value n q),q) = 0

namespace HillHminusZeroSequenceBall

def source (B : HillHminusZeroSequenceBall) : Set PeriodOneHminusOne := ball B.center B.radius

theorem source_open (B : HillHminusZeroSequenceBall) : IsOpen B.source := isOpen_ball

theorem value_eq_on_overlap (B C : HillHminusZeroSequenceBall) (n : ℕ+) :
    EqOn (B.value n) (C.value n) (B.source ∩ C.source) := by
  intro q hq
  have hreal : ∃ a ∈ B.source ∩ C.source, IsRealPeriodOneHminusOne a :=
    exists_real_mem_periodOneHminus_ball_inter B.center C.center B.center_real C.center_real
      B.radius C.radius ⟨q,hq⟩
  apply lp.ext
  funext m
  have hB : AnalyticOnNhd ℂ (fun a => B.value n a m) B.source :=
    fun a ha => ((lp.evalCLM ℂ (fun _ : ℕ+ => ℂ) 2 m).analyticAt _).comp (B.analytic_value n a ha)
  have hC : AnalyticOnNhd ℂ (fun a => C.value n a m) C.source :=
    fun a ha => ((lp.evalCLM ℂ (fun _ : ℕ+ => ℂ) 2 m).analyticAt _).comp (C.analytic_value n a ha)
  exact analytic_eqOn_of_real_periodOneHminus _ (B.source_open.inter C.source_open)
    ((convex_ball B.center B.radius).inter (convex_ball C.center C.radius)).isPreconnected hreal _ _
    (hB.mono inter_subset_left) (hC.mono inter_subset_right)
    (fun a ha har => congrArg (fun d : lp (fun _ : ℕ+ => ℂ) 2 => d m)
      ((B.real_eq n a ha.1 har).trans (C.real_eq n a ha.2 har).symm)) hq

end HillHminusZeroSequenceBall

theorem exists_hillHminusZeroSequenceBall (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) :
    ∃ B : HillHminusZeroSequenceBall, B.center = q ∧ q ∈ B.source := by
  obtain ⟨P,hq,_⟩ := exists_hillProductEquationPatch q hr
  obtain ⟨_,ε,_,hε,s,hs⟩ := P.exists_common_actual_analytic_zero_sequences q hq hr
  refine ⟨{
    center := q
    center_real := hr
    radius := ε
    radius_pos := hε
    subset := ?_
    value := s
    analytic_value := fun n => (hs n).1
    real_eq := fun n => (hs n).2.2.2.1
    root := fun n => (hs n).2.2.2.2
  },rfl,mem_ball_self hε⟩
  intro y hy
  exact mem_iUnion.mpr ⟨P.parent,P.subset ((hs 1).2.2.1 y hy).1.2⟩

end NLS.KdV
