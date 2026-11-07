import NLS.KdV.HillProductEquationCommonAnalyticZeros
import NLS.SequenceSpaces.PeriodOneHminusOneRealGermIdentity

/-! Common full-l2 analytic period solutions are ACTUAL intrinsic
numerator roots on the ENTIRE common complex source ball. Real germ
agreement is upgraded by native real-form analytic identity, without
assuming uniform real continuity before all numerator indices. -/
noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem common_analytic_sequence_canonical_root (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (_hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q)
    (ε : ℝ) (hε : 0 < ε) (n : ℕ+)
    (s : PeriodOneHminusOne → lp (fun _ : ℕ+ => ℂ) 2)
    (hs : AnalyticOnNhd ℂ s (ball q ε))
    (hgraph : ∀ y ∈ ball q ε, (s y,y) ∈ P.inputDomain)
    (hreal : ∀ᶠ a : PeriodOneRealHminusOne in 𝓝 ⟨q,hr⟩, s a.val = hillHminusPsiZeroDisplacement n a)
    (m : ℕ+) (hmn : m ≠ n) :
    ∀ y ∈ ball q ε, hillHminusCanonicalPsi n (hillEnergySequenceZero m (s y),y) = 0 := by
  let f : PeriodOneHminusOne → ℂ := fun y => hillHminusCanonicalPsi n (hillEnergySequenceZero m (s y),y)
  have hσ (y : PeriodOneHminusOne) (hy : y ∈ ball q ε) :
      AnalyticAt ℂ (fun z => hillEnergySequenceZero m (s z)) y := by
    have hev := ((lp.evalCLM ℂ (fun _ : ℕ+ => ℂ) 2 m).analyticAt (s y)).comp (hs y hy)
    change AnalyticAt ℂ (fun z => ((Real.pi:ℂ)*(m:ℕ))^2+(m:ℕ)*(s z m)) y
    exact analyticAt_const.add (analyticAt_const.mul hev)
  have hf : AnalyticOnNhd ℂ f (ball q ε) := by
    intro y hy
    have hdom : y ∈ hillHminusCanonicalPsiDomain := mem_iUnion.mpr ⟨P.parent,P.subset (hgraph y hy).2⟩
    exact (analyticOnNhd_hillHminusCanonicalPsi n _ ⟨mem_univ _,hdom⟩).comp
      ((hσ y hy).prod analyticAt_id)
  have he : ∀ᶠ a : PeriodOneRealHminusOne in 𝓝 ⟨q,hr⟩, f a.val = (0 : PeriodOneHminusOne → ℂ) a.val := by
    filter_upwards [hreal] with a ha
    change hillHminusCanonicalPsi n (hillEnergySequenceZero m (s a.val),a.val) = 0
    rw [ha,hillEnergySequenceZero_real]
    exact hillHminusCanonicalPsiRealZero_is_zero n m a.val a.property hmn
  exact analytic_eqOn_of_real_periodOneHminus_germ _ isOpen_ball (convex_ball q ε).isPreconnected
    q (mem_ball_self hε) hr f 0 hf (fun _ _ => analyticAt_const) he

end NLS.KdV.HillProductEquationPatch
