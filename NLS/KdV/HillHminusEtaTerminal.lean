import NLS.KdV.HillHminusOwnEtaAnalytic

/-! Exact literal spectral terminal of the SAME own-index eta coordinate.
No angle, gap division or unrelated root family is introduced. -/
noncomputable section
open Complex NLS.ZakharovShabat
namespace NLS.KdV.HillHminusPsiChart

def sourceEtaTerminal (P : HillHminusPsiChart) (n : ℤ) (q : PeriodOneHminusOne) : ℂ :=
  -2*(sourceDirichletMidpointDisplacement (by norm_num) (by norm_num) (P.dirichletSource q) n+
    I*sourceDirichletEtaSineNumerator (by norm_num) (by norm_num) n (P.dirichletSource q))

theorem sourceEtaSequence_unphase (P : HillHminusPsiChart)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num) P.family.originalDomain P.family.domain P.family.roots)
    (q : PeriodOneHminusOne) (hq : q∈P.sourceBetaDomain) (n : ℤ) :
    P.sourceEtaSequence q n*exp (-I*P.sourceOwnEtaRemainder n q)=P.sourceEtaTerminal n q := by
  rw [P.sourceEtaSequence_apply H q hq n]
  simp only [sourceGapWeightedEtaCoordinate,one_mul,sourceOwnEtaRemainder,sourceEtaTerminal,
    sourceDirichletMidpointDisplacement_apply]
  rw [mul_assoc,←exp_add,
    show I*sourceAngularEtaRemainder (by norm_num) (by norm_num) n P.family.roots (P.dirichletSource q)+
      -I*sourceAngularEtaRemainder (by norm_num) (by norm_num) n P.family.roots (P.dirichletSource q)=0 by ring,
    exp_zero,mul_one]

end NLS.KdV.HillHminusPsiChart
