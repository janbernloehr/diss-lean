import NLS.KdV.HillProductEquationPatches

/-! The FULL original weighted native Hill equation as an actual
lp2-valued function. Its coordinates are exactly the jointly analytic
scalar equations on the common placed-input domain. -/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

def row (P : HillProductEquationPatch) (n m : ℕ+)
    (t : lp (fun _ : ℕ+ => ℂ) 2 × PeriodOneHminusOne) : ℂ :=
  hillProductPeriodEquationRow n m P.centers P.radii
    (t.1,((P.parent.parent.miuraBall.actionBall.shift:ℂ),P.sourcePsi t.2))

theorem row_eq_native (P : HillProductEquationPatch) (n m : ℕ+)
    (t : lp (fun _ : ℕ+ => ℂ) 2 × PeriodOneHminusOne) :
    P.row n m t = P.parent.productEquationRow n m (P.centers ((m:ℕ):ℤ)) (P.radii ((m:ℕ):ℤ)) t := rfl

theorem analytic_row (P : HillProductEquationPatch) (n m : ℕ+) :
    AnalyticOnNhd ℂ (P.row n m) (univ ×ˢ P.source) :=
  P.parent.analytic_productEquationRow n m _ _ P.source P.subset (P.periods_analytic n ((m:ℕ):ℤ))

def equation (P : HillProductEquationPatch) (n : ℕ+)
    (t : lp (fun _ : ℕ+ => ℂ) 2 × PeriodOneHminusOne) : lp (fun _ : ℕ+ => ℂ) 2 :=
  if h : ∃ F : lp (fun _ : ℕ+ => ℂ) 2, ∀ m : ℕ+, F m = P.row n m t
  then Classical.choose h else 0

theorem equation_exists (P : HillProductEquationPatch) (n : ℕ+)
    (t : lp (fun _ : ℕ+ => ℂ) 2 × PeriodOneHminusOne) (ht : t ∈ P.inputDomain) :
    ∃ F : lp (fun _ : ℕ+ => ℂ) 2, ∀ m : ℕ+, F m = P.row n m t := by
  obtain ⟨_,_,hF⟩ := exists_hillProductPeriodEquationSequence P.quotients P.isolating P.V_open
    (P.sourcePsi t.2) (P.image t.2 ht.2).1 (P.image t.2 ht.2).2
    (P.parent.parent.miuraBall.actionBall.shift:ℂ) t.1 ht.1.2 P.centers P.radii P.radii_pos P.discs_eq
  obtain ⟨F,hFn,_⟩ := hF n
  exact ⟨F,hFn⟩

theorem equation_apply (P : HillProductEquationPatch) (n m : ℕ+)
    (t : lp (fun _ : ℕ+ => ℂ) 2 × PeriodOneHminusOne) (ht : t ∈ P.inputDomain) :
    P.equation n t m = P.row n m t := by
  have h := P.equation_exists n t ht
  simpa only [equation,dif_pos h] using Classical.choose_spec h m

theorem equation_eq_retained_add_single (P : HillProductEquationPatch) (n : ℕ+)
    (t : lp (fun _ : ℕ+ => ℂ) 2 × PeriodOneHminusOne) (ht : t ∈ P.inputDomain)
    (F : lp (fun _ : ℕ+ => ℂ) 2)
    (hF : ∀ m, F m = hillRetainedProductPeriodRow n m P.centers P.radii
      (t.1,((P.parent.parent.miuraBall.actionBall.shift:ℂ),P.sourcePsi t.2))) :
    P.equation n t = F+lp.single 2 n
      (t.1 n-hillEnergyMidpointDisplacement (P.parent.parent.miuraBall.actionBall.shift:ℂ) (P.sourcePsi t.2) n) := by
  ext m
  rw [P.equation_apply n m t ht]
  change P.row n m t = F m+(lp.single 2 n _ : lp (fun _ : ℕ+ => ℂ) 2) m
  rw [hF,lp.single_apply]
  by_cases hmn : m = n
  · subst m
    simp only [row,hillProductPeriodEquationRow,hillRetainedProductPeriodRow,ite_true,Pi.single_eq_same,zero_add]
  · simp only [row,hillProductPeriodEquationRow,hillRetainedProductPeriodRow,Pi.single_apply,if_neg hmn,add_zero]

theorem norm_equation_le_of_quotient_bound (P : HillProductEquationPatch)
    (t : lp (fun _ : ℕ+ => ℂ) 2 × PeriodOneHminusOne) (ht : t ∈ P.inputDomain)
    (Q : ℝ) (hQ : 0 ≤ Q)
    (hquot : ∀ k : ℤ, ∀ z ∈ P.discs k,
      ‖sourceSingleRootQuotientJointProduct (by norm_num) (by norm_num) k
        (z,(hillIndependentFrequencyDisplacement ((P.parent.parent.miuraBall.actionBall.shift:ℂ),t.1),P.sourcePsi t.2))‖ ≤ Q)
    (n : ℕ+) :
    ‖P.equation n t‖ ≤ (2*Real.pi*(Real.pi^2*P.separation*(P.separation*Q)))*
      (‖hillIndependentFrequencyDisplacement ((P.parent.parent.miuraBall.actionBall.shift:ℂ),t.1)‖+
        ‖sourcePeriodicMidpointDisplacement (by norm_num) (by norm_num) (P.sourcePsi t.2)‖+
        ‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (P.sourcePsi t.2)‖)+‖t.1‖+
      (2*Real.pi*‖sourcePeriodicMidpointDisplacement (by norm_num) (by norm_num) (P.sourcePsi t.2)‖+
        ‖sourcePeriodicMidpointDisplacement (by norm_num) (by norm_num) (P.sourcePsi t.2)‖^2+
        ‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (P.sourcePsi t.2)‖^2+
        ‖(P.parent.parent.miuraBall.actionBall.shift:ℂ)‖) := by
  obtain ⟨F,hFn,hFb⟩ := exists_hillRetainedProductPeriodSequence_of_quotient_bound P.quotients P.isolating
    (P.sourcePsi t.2) (P.image t.2 ht.2).1 (P.image t.2 ht.2).2
    (P.parent.parent.miuraBall.actionBall.shift:ℂ) t.1 ht.1.2 P.centers P.radii P.radii_pos P.discs_eq Q hQ hquot n
  rw [P.equation_eq_retained_add_single n t ht F hFn]
  have hv := (norm_sub_le (t.1 n) (hillEnergyMidpointDisplacement (P.parent.parent.miuraBall.actionBall.shift:ℂ) (P.sourcePsi t.2) n)).trans
    (add_le_add (lp.norm_apply_le_norm (by norm_num) t.1 n)
      (norm_hillEnergyMidpointDisplacement_le (P.parent.parent.miuraBall.actionBall.shift:ℂ) (P.sourcePsi t.2) n))
  have h := norm_add_le F (lp.single 2 n (t.1 n-hillEnergyMidpointDisplacement (P.parent.parent.miuraBall.actionBall.shift:ℂ) (P.sourcePsi t.2) n))
  rw [lp.norm_single (by norm_num : (0:ℝ≥0∞) < 2)] at h
  linarith

def frequencySource (P : HillProductEquationPatch)
    (t : lp (fun _ : ℕ+ => ℂ) 2 × PeriodOneHminusOne) : Coeff 2 × CoeffPair 2 :=
  (hillIndependentFrequencyDisplacement ((P.parent.parent.miuraBall.actionBall.shift:ℂ),t.1),P.sourcePsi t.2)

theorem analytic_frequencySource (P : HillProductEquationPatch) :
    AnalyticOnNhd ℂ P.frequencySource P.inputDomain := by
  intro t ht
  have hA := (analyticOnNhd_hillIndependentFrequencyDisplacement _ ht.1.1).comp
    (f := fun s : lp (fun _ : ℕ+ => ℂ) 2 × PeriodOneHminusOne => ((P.parent.parent.miuraBall.actionBall.shift:ℂ),s.1))
    (analyticAt_const.prod analyticAt_fst)
  have hψ := (P.analytic_sourcePsi t.2 ht.2).comp (f := Prod.snd) analyticAt_snd
  exact hA.prod hψ

end NLS.KdV.HillProductEquationPatch
