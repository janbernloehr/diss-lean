import NLS.KdV.HminusOneHillPsiIndexedZeroExtension

/-! Real-centered analytic charts for an ACTUAL indexed retained zero.
Their WHOLE complex overlaps agree by real-form uniqueness. The index
pair is fixed here; no common neighborhood before all pairs is assumed. -/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.KdV

structure HillHminusPsiZeroBall (n m : ℕ+) where
  center : PeriodOneHminusOne
  center_real : IsRealPeriodOneHminusOne center
  radius : ℝ
  radius_pos : 0 < radius
  subset : ball center radius ⊆ hillHminusCanonicalPsiDomain
  value : PeriodOneHminusOne → ℂ
  analytic_value : AnalyticOnNhd ℂ value (ball center radius)
  real_eq : ∀ q ∈ ball center radius, ∀ hq : IsRealPeriodOneHminusOne q,
    value q = (hillHminusCanonicalPsiRealZero n m q hq:ℂ)
  root : ∀ q ∈ ball center radius, hillHminusCanonicalPsi n (value q,q) = 0
  simple : ∀ q ∈ ball center radius,
    deriv (fun E : ℂ => hillHminusCanonicalPsi n (E,q)) (value q) ≠ 0

namespace HillHminusPsiZeroBall

def source {n m : ℕ+} (B : HillHminusPsiZeroBall n m) : Set PeriodOneHminusOne := ball B.center B.radius

theorem source_open {n m : ℕ+} (B : HillHminusPsiZeroBall n m) : IsOpen B.source := isOpen_ball

theorem value_eq_on_overlap {n m : ℕ+} (B C : HillHminusPsiZeroBall n m) :
    EqOn B.value C.value (B.source ∩ C.source) := by
  intro q hq
  have hreal : ∃ a ∈ B.source ∩ C.source, IsRealPeriodOneHminusOne a :=
    exists_real_mem_periodOneHminus_ball_inter B.center C.center B.center_real C.center_real
      B.radius C.radius ⟨q,hq⟩
  exact analytic_eqOn_of_real_periodOneHminus (B.source ∩ C.source) (B.source_open.inter C.source_open)
    ((convex_ball B.center B.radius).inter (convex_ball C.center C.radius)).isPreconnected hreal _ _
    (B.analytic_value.mono inter_subset_left) (C.analytic_value.mono inter_subset_right)
    (fun a ha har => (B.real_eq a ha.1 har).trans (C.real_eq a ha.2 har).symm) hq

end HillHminusPsiZeroBall

theorem exists_hillHminusPsiZeroBall (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q)
    (n m : ℕ+) (hmn : m ≠ n) :
    ∃ B : HillHminusPsiZeroBall n m, B.center = q ∧ q ∈ B.source := by
  obtain ⟨U,hU,hqU,hUD,s,hs,hreal,hroots⟩ := exists_local_analytic_indexed_hillHminusPsi_zero q hr n m hmn
  obtain ⟨r,hrpos,hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hqU)
  refine ⟨{
    center := q
    center_real := hr
    radius := r
    radius_pos := hrpos
    subset := hball.trans hUD
    value := s
    analytic_value := hs.mono hball
    real_eq := fun a ha har => hreal a (hball ha) har
    root := fun a ha => (hroots a (hball ha)).1
    simple := fun a ha => (hroots a (hball ha)).2
  },rfl,mem_ball_self hrpos⟩

end NLS.KdV
