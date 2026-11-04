import NLS.KdV.HillAbelianRealPatchCompatibility

/-! Real-centered native source balls are chosen BEFORE ALL Abelian
indices. Physical values from different original Miura patches agree
on WHOLE complex ball overlaps by the native real-form identity. -/
noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal Classical
namespace NLS.KdV

structure HillPhysicalAbelianSourceBall where
  patch : HillProductEquationPatch
  center : PeriodOneHminusOne
  center_real : IsRealPeriodOneHminusOne center
  radius : ℝ
  radius_pos : 0 < radius
  subset : ball center radius ⊆ patch.physicalDirichletSource

namespace HillPhysicalAbelianSourceBall

def source (B : HillPhysicalAbelianSourceBall) : Set PeriodOneHminusOne := ball B.center B.radius

def value (B : HillPhysicalAbelianSourceBall) (n m : ℕ+) : PeriodOneHminusOne → ℂ :=
  B.patch.physicalOffIndexAbelianValue n m

theorem source_open (B : HillPhysicalAbelianSourceBall) : IsOpen B.source := isOpen_ball

theorem analytic_value (B : HillPhysicalAbelianSourceBall) (n m : ℕ+) (hmn : m ≠ n) :
    AnalyticOnNhd ℂ (B.value n m) B.source :=
  (B.patch.analytic_physicalOffIndexAbelianValue n m hmn).mono B.subset

theorem value_eq_on_overlap (B C : HillPhysicalAbelianSourceBall) (n m : ℕ+) (hmn : m ≠ n) :
    EqOn (B.value n m) (C.value n m) (B.source ∩ C.source) := by
  intro q hq
  have hreal : ∃ a ∈ B.source ∩ C.source, IsRealPeriodOneHminusOne a :=
    exists_real_mem_periodOneHminus_ball_inter B.center C.center B.center_real C.center_real
      B.radius C.radius ⟨q,hq⟩
  exact analytic_eqOn_of_real_periodOneHminus _ (B.source_open.inter C.source_open)
    ((convex_ball B.center B.radius).inter (convex_ball C.center C.radius)).isPreconnected hreal _ _
    ((B.analytic_value n m hmn).mono inter_subset_left) ((C.analytic_value n m hmn).mono inter_subset_right)
    (fun a ha har => B.patch.physicalOffIndexAbelianValue_eq_of_real_overlap C.patch n m hmn a
      (B.subset ha.1).1 (C.subset ha.2).1 har) hq

end HillPhysicalAbelianSourceBall

theorem exists_hillPhysicalAbelianSourceBall_of_patch (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) :
    ∃ B : HillPhysicalAbelianSourceBall, B.patch = P ∧ B.center = q ∧ q ∈ B.source := by
  obtain ⟨r,hrpos,hsub⟩ := Metric.isOpen_iff.mp P.physicalDirichletSource_open q
    (P.real_mem_physicalDirichletSource q hq hr)
  exact ⟨⟨P,q,hr,r,hrpos,hsub⟩,rfl,rfl,mem_ball_self hrpos⟩

theorem exists_hillPhysicalAbelianSourceBall (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) :
    ∃ B : HillPhysicalAbelianSourceBall, B.center = q ∧ q ∈ B.source := by
  obtain ⟨P,hq,_⟩ := exists_hillProductEquationPatch q hr
  obtain ⟨B,_,hc,hB⟩ := exists_hillPhysicalAbelianSourceBall_of_patch P q hq hr
  exact ⟨B,hc,hB⟩

end NLS.KdV
