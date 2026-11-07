import NLS.KdV.HillMiuraCentralMean
import NLS.KdV.HillMiuraCentralLowerBound

/-! Actual Hill/Miura action comparison also at zero central frequency.
A small real constant perturbation opens the central gap, and continuity
in the ORIGINAL L2 and Hminus norms removes the exterior-shift premise.
The original positive labels and factor two higher-action normalization
are retained, including every collapsed positive gap. -/
noncomputable section
open Set Filter Topology Complex NLS.ZakharovShabat
open scoped ComplexConjugate
namespace NLS.KdV

def realL2AddConstant (u : PeriodOneRealL2) (c : ℝ) : PeriodOneRealL2 :=
  ⟨u.val+lp.single 2 0 (c:ℂ),by
    intro k
    by_cases hk : k=0
    · subst k
      simp only [lp.coeFn_add,Pi.add_apply,lp.single_apply,Pi.single_apply,neg_zero,
        ite_true,map_add,conj_ofReal]
      exact congrArg (fun z : ℂ => z+(c:ℂ)) (u.property 0)
    · simpa only [lp.coeFn_add,Pi.add_apply,lp.single_apply,Pi.single_apply,
        if_neg hk,if_neg (neg_ne_zero.mpr hk),add_zero,map_add,map_zero] using u.property k⟩

theorem tendsto_realL2AddConstant_zero (u : PeriodOneRealL2) :
    Tendsto (fun c : ℝ => (realL2AddConstant u c).val) (𝓝 0) (𝓝 u.val) := by
  have h : Continuous (fun c : ℝ => u.val+lp.single 2 0 (c:ℂ)) :=
    continuous_const.add ((lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) 2 0).continuous.comp continuous_ofReal)
  simpa only [realL2AddConstant,Complex.ofReal_zero,lp.single_zero,add_zero] using h.continuousAt.tendsto (x := 0)

/-- No exterior-shift assumption: the comparison includes mean-zero lifts. -/
theorem hillHminusCanonicalAction_eq_Miura_of_real_all
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q)
    (u : PeriodOneRealL2) (c : ℝ)
    (himage : periodOneMiura u.val=q+periodOneL2Inclusion (lp.single 2 0 (c:ℂ))) (n : ℕ+) :
    hillHminusCanonicalAction n q=hillHminusMiuraIndexedAction u.val (n:ℕ) := by
  by_cases hu0 : u.val 0=0
  · let ε : ℕ → ℝ := fun k => 1/((k:ℝ)+1)
    let v : ℕ → PeriodOneRealL2 := fun k => realL2AddConstant u (ε k)
    have hε : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have hv : Tendsto (fun k => (v k).val) atTop (𝓝 u.val) :=
      (tendsto_realL2AddConstant_zero u).comp hε
    let a : ℕ → PeriodOneHminusOne := fun k => periodOneMiura (v k).val-
      periodOneL2Inclusion (lp.single 2 0 (c:ℂ))
    have ha : Tendsto a atTop (𝓝 q) := by
      have h := (continuous_periodOneMiura.continuousAt.tendsto.comp hv).sub_const
        (periodOneL2Inclusion (lp.single 2 0 (c:ℂ)))
      rw [himage,add_sub_cancel_right] at h
      exact h
    have hL : Tendsto (fun k => hillHminusCanonicalAction n (a k)) atTop
        (𝓝 (hillHminusCanonicalAction n q)) :=
      ((analyticOnNhd_hillHminusCanonicalAction n q
        (real_mem_hillHminusCanonicalActionDomain q hq)).continuousAt.tendsto).comp ha
    have hR := tendsto_hillHminusMiuraIndexedAction_of_bounded_coefficients v u
      (Metric.isBounded_range_of_tendsto _ hv)
      (fun j => (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 j).continuous.continuousAt.tendsto.comp hv) (n:ℕ)
    have he : (fun k => hillHminusCanonicalAction n (a k))=
        (fun k => hillHminusMiuraIndexedAction (v k).val (n:ℕ)) := by
      funext k
      have hi : periodOneMiura (v k).val=a k+
          periodOneL2Inclusion (lp.single 2 0 (c:ℂ)) := by dsimp [a]; abel
      have hz : (0:ℂ) ∉ periodicSpectrum (by simp) (periodOnePotential (hillMiuraDiagonal (v k).val)) := by
        rw [hillMiura_zero_mem_spectrum_iff_mean_zero]
        have hp : 0 < ε k := by dsimp [ε]; positivity
        simpa only [v,realL2AddConstant,lp.coeFn_add,Pi.add_apply,lp.single_apply,
          Pi.single_apply,ite_true,hu0,zero_add,Complex.ofReal_eq_zero] using ne_of_gt hp
      exact hillHminusCanonicalAction_eq_Miura_of_real (a k)
        ((periodOneMiura_real (v k).val (v k).property).sub (periodOneL2Inclusion_single_zero_real c))
        (v k) c hi (shift_outside_of_zero_not_mem_hillMiura_spectrum (a k) (v k).val (c:ℂ) hi hz) n
    rw [he] at hL
    exact tendsto_nhds_unique hL hR
  · have hz : (0:ℂ) ∉ periodicSpectrum (by simp) (periodOnePotential (hillMiuraDiagonal u.val)) :=
      fun hz => hu0 ((hillMiura_zero_mem_spectrum_iff_mean_zero u).mp hz)
    exact hillHminusCanonicalAction_eq_Miura_of_real q hq u c himage
      (shift_outside_of_zero_not_mem_hillMiura_spectrum q u.val (c:ℂ) himage hz) n

end NLS.KdV
