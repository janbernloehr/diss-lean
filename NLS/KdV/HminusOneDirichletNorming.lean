import NLS.KdV.HminusOneCanonicalDirichlet
import NLS.MKdV.QuasiHillL2NormingTrace

/-! Nonzero analytic Dirichlet norming multipliers on the existing common
domain. Independence follows from the actual physical terminal derivative
on the dense original L2 potentials, then continuity on complex overlaps. -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology NLS.ZakharovShabat NLS.MKdV
open scoped Classical
namespace NLS.KdV

namespace HillHminusDirichletBall

def norming (B : HillHminusDirichletBall) (n : ℕ+) (q : PeriodOneHminusOne) : ℂ :=
  quasiHillL2DirichletTerminal (B.miuraBall.actionBall.lift q)
    (B.energy n q+(B.miuraBall.actionBall.shift : ℂ))

theorem analytic_norming (B : HillHminusDirichletBall) (n : ℕ+) :
    AnalyticOnNhd ℂ (B.norming n) B.source := by
  intro q hq
  exact (analyticOnNhd_quasiHillL2DirichletTerminal_joint
    (B.energy n q+(B.miuraBall.actionBall.shift : ℂ),B.miuraBall.actionBall.lift q)
    (mem_univ _)).comp (f := fun a =>
      (B.energy n a+(B.miuraBall.actionBall.shift : ℂ),B.miuraBall.actionBall.lift a))
      (((B.analytic_energy n q hq).add analyticAt_const).prod
        (B.miuraBall.actionBall.lift_analytic q hq))

theorem quasi_root (B : HillHminusDirichletBall) (n : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ B.source) :
    quasiHillL2Dirichlet (B.miuraBall.actionBall.lift q)
      (B.energy n q+(B.miuraBall.actionBall.shift : ℂ)) = 0 := by
  rw [← hillHminusDirichlet_eq_miura_of_shifted_image q _ _ _ (B.miuraBall.actionBall.image q hq)]
  exact B.energy_is_root n q hq

theorem norming_ne_zero (B : HillHminusDirichletBall) (n : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ B.source) : B.norming n q ≠ 0 :=
  quasiHillL2DirichletTerminal_ne_zero _ _ (B.quasi_root n q hq)

theorem norming_eq_hillL2 (B : HillHminusDirichletBall) (n : ℕ+) (q : Coeff 2)
    (hq : periodOneL2Inclusion q ∈ B.source) :
    B.norming n (periodOneL2Inclusion q) = hillL2DirichletTerminal (Coeff.periodDouble q)
      (B.energy n (periodOneL2Inclusion q)) := by
  apply quasiHillL2DirichletTerminal_eq_hillL2_of_shifted_root
  · rw [map_add]
    exact B.miuraBall.actionBall.image _ hq
  · exact B.quasi_root n _ hq

theorem norming_eq_on_overlap (B C : HillHminusDirichletBall) (n : ℕ+) :
    EqOn (B.norming n) (C.norming n) (B.source ∩ C.source) := by
  apply eqOn_of_eqOn_periodOneL2Inclusion (B.source_open.inter C.source_open)
  · exact (B.analytic_norming n).continuousOn.mono inter_subset_left
  · exact (C.analytic_norming n).continuousOn.mono inter_subset_right
  · intro q hq
    rw [B.norming_eq_hillL2 n q hq.1,C.norming_eq_hillL2 n q hq.2,
      B.energy_eq_on_overlap C n hq]

end HillHminusDirichletBall

/-- Actual terminal Dirichlet multiplier, glued on the SAME common domain. -/
def hillHminusDirichletNorming (n : ℕ+) (q : PeriodOneHminusOne) : ℂ :=
  if hq : q ∈ hillHminusCanonicalDirichletDomain then
    (Classical.choose (mem_iUnion.mp hq)).norming n q
  else 0

theorem HillHminusDirichletBall.canonical_norming_eq (B : HillHminusDirichletBall) (n : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ B.source) : hillHminusDirichletNorming n q = B.norming n q := by
  have hdom : q ∈ hillHminusCanonicalDirichletDomain := mem_iUnion.mpr ⟨B,hq⟩
  rw [hillHminusDirichletNorming,dif_pos hdom]
  let C : HillHminusDirichletBall := Classical.choose (mem_iUnion.mp hdom)
  have hC : q ∈ C.source := Classical.choose_spec (mem_iUnion.mp hdom)
  exact C.norming_eq_on_overlap B n ⟨hC,hq⟩

theorem analyticOnNhd_hillHminusDirichletNorming (n : ℕ+) :
    AnalyticOnNhd ℂ (hillHminusDirichletNorming n) hillHminusCanonicalDirichletDomain := by
  intro q hq
  obtain ⟨B,hB⟩ := mem_iUnion.mp hq
  apply (B.analytic_norming n q hB).congr
  filter_upwards [B.source_open.mem_nhds hB] with a ha
  exact (B.canonical_norming_eq n a ha).symm

theorem hillHminusDirichletNorming_ne_zero (n : ℕ+) (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusCanonicalDirichletDomain) : hillHminusDirichletNorming n q ≠ 0 := by
  obtain ⟨B,hB⟩ := mem_iUnion.mp hq
  rw [B.canonical_norming_eq n q hB]
  exact B.norming_ne_zero n q hB

/-- On physical L2 potentials it is the derivative of the normalized scalar solution. -/
theorem hillHminusDirichletNorming_eq_hillL2 (n : ℕ+) (q : Coeff 2)
    (hq : periodOneL2Inclusion q ∈ hillHminusCanonicalDirichletDomain) :
    hillHminusDirichletNorming n (periodOneL2Inclusion q) =
      hillL2DirichletTerminal (Coeff.periodDouble q)
        (hillHminusCanonicalDirichlet n (periodOneL2Inclusion q)) := by
  obtain ⟨B,hB⟩ := mem_iUnion.mp hq
  rw [B.canonical_norming_eq n _ hB,B.canonical_dirichlet_eq n _ hB]
  exact B.norming_eq_hillL2 n q hB

/-- The dense H1 comparison retains an arbitrary complex energy shift. -/
theorem hillHminusDirichletNorming_eq_shifted_sobolev (n : ℕ+) (b : ScalarDomain 2) (c : ℂ)
    (hq : periodOneMiura (scalarInclusion b)-periodOneL2Inclusion (lp.single 2 0 c) ∈
      hillHminusCanonicalDirichletDomain) :
    hillHminusDirichletNorming n
      (periodOneMiura (scalarInclusion b)-periodOneL2Inclusion (lp.single 2 0 c)) =
    quasiHillL2DirichletTerminal (scalarInclusion b)
      (hillHminusCanonicalDirichlet n
        (periodOneMiura (scalarInclusion b)-periodOneL2Inclusion (lp.single 2 0 c))+c) := by
  let v : Coeff 2 := sobolevMiuraUnitPotential b-lp.single 2 0 c
  have hv : periodOneMiura (scalarInclusion b)-periodOneL2Inclusion (lp.single 2 0 c) =
      periodOneL2Inclusion v := by
    dsimp only [v]
    rw [periodOneMiura_scalarInclusion,map_sub]
  have himage : periodOneMiura (scalarInclusion b) = periodOneL2Inclusion (v+lp.single 2 0 c) := by
    dsimp only [v]
    rw [sub_add_cancel,← periodOneMiura_scalarInclusion]
  have hvdom : periodOneL2Inclusion v ∈ hillHminusCanonicalDirichletDomain := hv ▸ hq
  have hroot : quasiHillL2Dirichlet (scalarInclusion b)
      (hillHminusCanonicalDirichlet n (periodOneL2Inclusion v)+c) = 0 := by
    rw [← hillHminusDirichlet_eq_miura_of_shifted_image _ _ _ _ (by
      rw [← map_add]
      exact himage)]
    exact hillHminusCanonicalDirichlet_is_root n _ hvdom
  rw [hv,hillHminusDirichletNorming_eq_hillL2 n v hvdom]
  exact (quasiHillL2DirichletTerminal_eq_hillL2_of_shifted_root _ v c _ himage hroot).symm

end NLS.KdV
