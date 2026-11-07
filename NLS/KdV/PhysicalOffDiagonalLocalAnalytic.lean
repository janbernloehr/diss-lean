import NLS.KdV.PhysicalOffDiagonalFrequency

/-! Individual actual atlas moments make the paired off-diagonal
physical correction analytic on one rough-source neighborhood at each
real base, simultaneously for every frequency. -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.ZakharovShabat
namespace NLS.KdV.PhysicalMiuraFrequencyChart

theorem exists_local_analytic_offDiagonal
    (B : PhysicalMiuraFrequencyChart) (q : PeriodOneHminusOne) (hq : q∈B.domain)
    (hr : IsRealPeriodOneHminusOne q) :
    ∃ T : Set PeriodOneHminusOne, IsOpen T ∧ q∈T ∧ T⊆B.domain ∧
      ∀ n : ℕ+, AnalyticOnNhd ℂ (B.offDiagonalCorrection n) T := by
  let F := fun a : PeriodOneHminusOne => hillMiuraDiagonal (B.psi.miura.lift a)
  have hF : AnalyticOnNhd ℂ F B.domain := fun a ha =>
    (hillMiuraDiagonal.analyticAt _).comp (B.psi.miura.lift_analytic a (B.domain_subset ha).1)
  let T := B.domain∩F ⁻¹' B.atlas.domain
  have hT : IsOpen T := hF.continuousOn.isOpen_inter_preimage B.domain_open B.atlas.isOpen_domain
  have hqr := isRealType_hillMiuraDiagonal ⟨B.psi.miura.lift q,B.real_lift q (B.domain_subset hq).1 hr⟩
  refine ⟨T,hT,⟨hq,B.atlas.realType_subset_domain hqr⟩,inter_subset_left,?_⟩
  intro n a ha
  have hfull := B.analytic_moments (n : ℤ) a ha.1
  have hn := (B.atlas.analytic_moment (n : ℤ) (n : ℤ) 2 (F a) ha.2).comp (hF a ha.1)
  have hm := (B.atlas.analytic_moment (n : ℤ) (-(n : ℤ)) 2 (F a) ha.2).comp (hF a ha.1)
  exact analyticAt_const.mul (hfull.sub (analyticAt_const.mul (hn.sub hm)))

end NLS.KdV.PhysicalMiuraFrequencyChart
