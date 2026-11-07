import NLS.KdV.HillHminusRetainedMiuraEtaChart

noncomputable section
open Complex
open scoped ENNReal
namespace NLS.KdV.HillHminusPsiChart

theorem retained_miura_nonzero_equation (P : HillHminusPsiChart)
    (q : PeriodOneHminusOne) (hq : q∈P.miura.domain) (n : ℤ) (hn : n≠0) :
    2*I*(Real.pi:ℂ)*n*P.miura.lift q n+
      ∑' j : ℤ,P.miura.lift q (n-j)*P.miura.lift q j=q.val n := by
  have he := congrArg (fun a : PeriodOneHminusOne => a.val n) (P.miura.image q hq)
  change (periodOneMiura (P.miura.lift q)).val n=
    q.val n+(periodOneL2Inclusion (lp.single 2 0 P.miura.energyShift)).val n at he
  rw [periodOneMiura_apply,periodOneL2Inclusion_apply] at he
  simpa only [lp.single_apply,Pi.single_apply,if_neg hn,add_zero] using he

end NLS.KdV.HillHminusPsiChart
