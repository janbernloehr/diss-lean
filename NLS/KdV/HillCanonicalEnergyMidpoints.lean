import NLS.KdV.HillCanonicalZeroSequencePeriods

/-! The filled diagonal of the canonical zero sequences is the
intrinsic original Hill energy midpoint. It is analytic on the COMMON
complex zero-sequence domain and agrees with every valid local Miura
midpoint formula wherever its full period equation is satisfied. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV

def hillHminusCanonicalEnergyMidpoint (m : ℕ+) (q : PeriodOneHminusOne) : ℂ :=
  hillEnergySequenceZero m (hillHminusCanonicalZeroSequence m q)

theorem analyticOnNhd_hillHminusCanonicalEnergyMidpoint (m : ℕ+) :
    AnalyticOnNhd ℂ (hillHminusCanonicalEnergyMidpoint m) hillHminusCanonicalZeroSequenceDomain := by
  intro q hq
  have he := ((lp.evalCLM ℂ (fun _ : ℕ+ => ℂ) 2 m).analyticAt _).comp (analyticOnNhd_hillHminusCanonicalZeroSequence m q hq)
  exact analyticAt_const.add (analyticAt_const.mul he)

theorem hillHminusCanonicalEnergyMidpoint_real (m : ℕ+) (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) :
    hillHminusCanonicalEnergyMidpoint m q =
      ((hillHminusLabels q hr (2*(m:ℕ)-1):ℂ)+(hillHminusLabels q hr (2*(m:ℕ)):ℂ))/2 := by
  rw [hillHminusCanonicalEnergyMidpoint,hillHminusCanonicalZeroSequence_real m q hr,hillEnergySequenceZero_real]
  simp [hillHminusCanonicalPsiRealZero]

theorem HillProductEquationPatch.equation_zero_omitted_energy_midpoint (P : HillProductEquationPatch)
    (m : ℕ+) (q : PeriodOneHminusOne) (d : lp (fun _ : ℕ+ => ℂ) 2)
    (ht : (d,q) ∈ P.inputDomain) (hF : P.equation m (d,q) = 0) :
    hillEnergySequenceZero m d = P.parent.parent.miuraBall.energyMidpoint m q := by
  have he := congrArg (fun F : lp (fun _ : ℕ+ => ℂ) 2 => F m) hF
  rw [P.equation_apply m m (d,q) ht] at he
  change P.row m m (d,q) = 0 at he
  simp only [HillProductEquationPatch.row,hillProductPeriodEquationRow,ite_true] at he
  have hd : d m = hillEnergyMidpointDisplacement (P.parent.parent.miuraBall.actionBall.shift:ℂ) (P.sourcePsi q) m := sub_eq_zero.mp he
  unfold hillEnergySequenceZero
  rw [hd]
  unfold hillEnergyMidpointDisplacement HillHminusMiuraGapBall.energyMidpoint
  have hm : ((m:ℕ):ℂ) ≠ 0 := by exact_mod_cast m.ne_zero
  change ((Real.pi:ℂ)*(m:ℕ))^2+(m:ℕ)*((_+_/4-_-((Real.pi:ℂ)*(m:ℕ))^2)/(m:ℕ)) = _+_/4-_
  dsimp only [HillProductEquationPatch.sourcePsi]
  field_simp [hm]
  ring

theorem HillProductEquationPatch.canonical_energyMidpoint_eq_local (P : HillProductEquationPatch)
    (m : ℕ+) (q : PeriodOneHminusOne)
    (ht : (hillHminusCanonicalZeroSequence m q,q) ∈ P.inputDomain)
    (hF : P.equation m (hillHminusCanonicalZeroSequence m q,q) = 0) :
    hillHminusCanonicalEnergyMidpoint m q = P.parent.parent.miuraBall.energyMidpoint m q :=
  P.equation_zero_omitted_energy_midpoint m q _ ht hF

end NLS.KdV
