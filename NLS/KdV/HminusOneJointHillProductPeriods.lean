import NLS.KdV.HillProductCommonPeriodCircles
import NLS.KdV.HminusOneHillProductPeriodEquations
import NLS.KdV.HillMiuraGapMidpoints

/-! Joint analytic literal product periods on the ORIGINAL native
H-minus-one topology. A fixed real-preserving analytic Miura lift
retains the physical energy shift and quadratic 2z Jacobian. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV
namespace HillHminusPsiBall

def productPeriod (B : HillHminusPsiBall) (n : ℕ+) (a : ℝ) (R : ℝ)
    (t : lp (fun _ : ℕ+ => ℂ) 2 × PeriodOneHminusOne) : ℂ :=
  hillEnergyProductJointPeriod n (a:ℂ) R (t.1,((B.parent.miuraBall.actionBall.shift:ℂ),
    hillMiuraDiagonal (B.parent.miuraBall.actionBall.lift t.2)))

theorem productPeriod_eq_fixed (B : HillHminusPsiBall) (n : ℕ+) (k : ℤ)
    (q : PeriodOneHminusOne)
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num)
      (hillMiuraDiagonal (B.parent.miuraBall.actionBall.lift q)) k)
    (d : lp (fun _ : ℕ+ => ℂ) 2) :
    B.productPeriod n D.center D.radius (d,q) =
      hillEnergyProductFixedPeriod n (B.parent.miuraBall.actionBall.shift:ℂ)
        (hillMiuraDiagonal (B.parent.miuraBall.actionBall.lift q)) D d := rfl

theorem analytic_productPeriod (B : HillHminusPsiBall) (n : ℕ+) (a : ℝ) (R : ℝ)
    (V : Set (CoeffPair 2))
    (hP : AnalyticOnNhd ℂ (hillEnergyProductJointPeriod n (a:ℂ) R) (univ ×ˢ (univ ×ˢ V)))
    (U : Set PeriodOneHminusOne) (hUB : U ⊆ B.source)
    (himage : ∀ q ∈ U, hillMiuraDiagonal (B.parent.miuraBall.actionBall.lift q) ∈ V) :
    AnalyticOnNhd ℂ (B.productPeriod n a R) (univ ×ˢ U) := by
  intro t ht
  have hlift := (B.parent.miuraBall.actionBall.lift_analytic t.2 (B.subset (hUB ht.2)).1).comp
    (f := Prod.snd) analyticAt_snd
  have hψ := (hillMiuraDiagonal.analyticAt _).comp hlift
  exact (hP _ ⟨mem_univ _,mem_univ _,himage t.2 ht.2⟩).comp
    (f := fun s : lp (fun _ : ℕ+ => ℂ) 2 × PeriodOneHminusOne =>
      (s.1,((B.parent.miuraBall.actionBall.shift:ℂ),hillMiuraDiagonal (B.parent.miuraBall.actionBall.lift s.2))))
    (analyticAt_fst.prod (analyticAt_const.prod hψ))

end HillHminusPsiBall

theorem exists_hminus_hill_product_joint_period_chart (q₀ : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q₀) :
    ∃ B : HillHminusPsiBall, B.center = q₀ ∧
    ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ q₀ ∈ U ∧ U ⊆ B.source ∧
    ∃ a R : ℤ → ℝ, (∀ m : ℤ, 0 < R m) ∧
      (∀ q ∈ U, ∀ m : ℤ,
        ∃ D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num)
          (hillMiuraDiagonal (B.parent.miuraBall.actionBall.lift q)) m,
          D.center = a m ∧ D.radius = R m) ∧
      ∀ (n : ℕ+) (m : ℤ), AnalyticOnNhd ℂ (B.productPeriod n (a m) (R m)) (univ ×ˢ U) := by
  obtain ⟨A⟩ := nonempty_miuraHillPsiFamily
  obtain ⟨B,_,hcenter,hqB⟩ := exists_hillHminusPsiBall A q₀ hr
  let T : PeriodOneHminusOne → CoeffPair 2 := fun q => hillMiuraDiagonal (B.parent.miuraBall.actionBall.lift q)
  let u : PeriodOneRealL2 := ⟨B.parent.miuraBall.actionBall.lift q₀,
    B.parent.miuraBall.actionBall.lift_real q₀ (B.subset hqB).1 hr⟩
  obtain ⟨V,hV,hTV,a,R,hR,hCircles,hPeriods⟩ :=
    exists_hillEnergyProduct_common_period_neighborhood (T q₀) (hillMiuraRealSource u).property
  have hT : AnalyticOnNhd ℂ T B.source := by
    intro q hq
    exact (hillMiuraDiagonal.analyticAt _).comp (B.parent.miuraBall.actionBall.lift_analytic q (B.subset hq).1)
  let U := B.source ∩ T ⁻¹' V
  have hU : IsOpen U := hT.continuousOn.isOpen_inter_preimage B.source_open hV
  refine ⟨B,hcenter,U,hU,⟨hqB,hTV⟩,inter_subset_left,a,R,hR,?_,?_⟩
  · intro q hq m
    exact hCircles (T q) hq.2 m
  · intro n m
    exact B.analytic_productPeriod n (a m) (R m) V (hPeriods n m) U inter_subset_left
      (fun _ hq => hq.2)

end NLS.KdV
