import NLS.ComplexAnalysis.CompactSliceBounds
import NLS.KdV.HillHminusOneCriticalControl
import NLS.KdV.HillHminusOnePrimitiveStrip
import NLS.ComplexAnalysis.CoshStripBounds
import NLS.ZakharovShabat.SourceSection8SineEstimates

/-! # Uniform actual rough Hill primitive bounds on every original contour -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV
namespace HillHminusAllContourPeriodData
variable {C : HillHminusMiuraChart} {N : ℕ} {V : Set PeriodOneHminusOne}
variable (D : HillHminusAllContourPeriodData C N V)
include D

omit D in
private theorem shifted_primitive_analytic (k : ℕ+) :
    AnalyticOnNhd ℂ (fun t : ℂ × PeriodOneHminusOne =>
      hillHminusContinuedPrimitive (t.1^2,t.2)+I*(k : ℂ)*Real.pi)
      ((fun t : ℂ × PeriodOneHminusOne => (t.1^2,t.2)) ⁻¹' hillHminusContinuationDomain) := by
  intro t ht
  exact ((analyticOnNhd_hillHminusContinuedPrimitive (t.1^2,t.2) ht).comp
    (f := fun u : ℂ × PeriodOneHminusOne => (u.1^2,u.2))
    ((analyticAt_fst.pow 2).prod analyticAt_snd)).add analyticAt_const

omit D in
private theorem shifted_primitive_free_bound (k : ℕ+) (z : ℂ)
    (hz : z ∈ sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4)) :
    ‖hillHminusContinuedPrimitive (z^2,0)+I*(k : ℂ)*Real.pi‖ < Real.pi/4+1 := by
  have he : hillHminusContinuedPrimitive (z^2,0)+I*(k : ℂ)*Real.pi =
      -I*(z-(Real.pi : ℂ)*(k : ℕ)) := by
    rw [hillHminusContinuedPrimitive_base,
      show -I*Complex.sqrt (z^2) = -I*z from
        classicalHillFreePrimitive_sq_of_re_pos z
          (re_pos_of_high_closedBall _ k.property z (sphere_subset_closedBall hz))]
    ring
  rw [he,norm_mul,norm_neg,norm_I,one_mul,mem_sphere_iff_norm.mp hz]
  linarith

private theorem exists_fixed_primitive_bound (k : ℕ+) : ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ 0 ∈ U ∧
    ∀ q ∈ U, ∀ z ∈ sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4),
      ‖hillHminusContinuedPrimitive (z^2,q)+I*(k : ℂ)*Real.pi‖ ≤ (Real.pi/4+1) := by
  exact exists_compact_slice_norm_bound
    (fun t : ℂ × PeriodOneHminusOne => hillHminusContinuedPrimitive (t.1^2,t.2)+I*(k : ℂ)*Real.pi)
    ((fun t : ℂ × PeriodOneHminusOne => (t.1^2,t.2)) ⁻¹' hillHminusContinuationDomain)
    (isOpen_hillHminusContinuationDomain.preimage ((continuous_fst.pow 2).prodMk continuous_snd))
    (shifted_primitive_analytic k).continuousOn _ (isCompact_sphere _ _) 0 (Real.pi/4+1)
    (D.cover k 0 D.zero_mem) (shifted_primitive_free_bound k)

theorem exists_uniform_primitive_bound :
    ∃ U : Set PeriodOneHminusOne, ∃ A : ℝ,
      U ⊆ V ∧ IsOpen U ∧ 0 ∈ U ∧ 0 < A ∧
        ∀ q ∈ U, ∀ k : ℕ+, ∀ z ∈ sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4),
          ‖hillHminusContinuedPrimitive (z^2,q)+I*(k : ℂ)*Real.pi‖ ≤ A := by
  obtain ⟨Nt,Vt,_,hVt,h0Vt,htrace⟩ := exists_hillHminus_disc_trace_approximation 0
    (Real.pi/4) (by positivity) le_rfl 1 (by norm_num)
  obtain ⟨Ns,Vs,_,hVs,h0Vs,hstrip⟩ := exists_hillHminus_high_primitive_strip 0
  let M := max Nt Ns
  let Ah : ℝ := 2*Real.exp (Real.pi/4)+2+Real.pi/2
  let Al : ℝ := Real.pi/4+1
  have hAh : 0 < Ah := by dsimp only [Ah];positivity
  have hAl : 0 < Al := by dsimp only [Al];positivity
  have hhigh (q : PeriodOneHminusOne) (hq : q ∈ V ∩ (Vt ∩ Vs))
      (k : ℕ+) (hk : M ≤ (k : ℕ)) (z : ℂ)
      (hz : z ∈ sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4)) :
      ‖hillHminusContinuedPrimitive (z^2,q)+I*(k : ℂ)*Real.pi‖ ≤ Ah := by
    let w := hillHminusContinuedPrimitive (z^2,q)+I*(k : ℂ)*Real.pi
    have hcover := D.cover k q hq.1 z hz
    have him : |w.im| < Real.pi/2 := hstrip q hq.2.2 (k : ℕ) ((le_max_right _ _).trans hk)
      z (sphere_subset_closedBall hz) hcover
    have hi : |z.im| ≤ Real.pi/4 := freeCircle_im_le _ (k : ℤ) z (by simpa only [Int.cast_natCast] using hz)
    have he := htrace q hq.2.1 (k : ℕ) ((le_max_left _ _).trans hk) z (sphere_subset_closedBall hz)
    have hcos : ‖cos z‖ ≤ Real.exp (Real.pi/4) :=
      (section8_norm_cos_le_exp_abs_im z).trans (Real.exp_le_exp.mpr hi)
    have hdelta : ‖hillHminusDiscriminant q (z^2)‖ ≤ 1+2*Real.exp (Real.pi/4) := by
      have hh := norm_le_norm_sub_add (hillHminusDiscriminant q (z^2)) (2*cos z)
      rw [norm_mul,norm_ofNat] at hh
      linarith
    have hc : 2*cosh w = (-1 : ℂ)^(k : ℕ)*hillHminusDiscriminant q (z^2) := by
      dsimp only [w]
      rw [cosh_add_hill_index]
      linear_combination (-1 : ℂ)^(k : ℕ)*(hillHminusContinuedPrimitive_trace _ hcover).1
    have hn := congrArg norm hc
    simp only [norm_mul,norm_ofNat,norm_pow,norm_neg,norm_one,one_pow,one_mul] at hn
    have hb := norm_le_two_norm_cosh_add_abs_im w
    change ‖w‖ ≤ Ah
    dsimp only [Ah]
    linarith
  have hfixed (k : ℕ+) : ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ 0 ∈ U ∧
      ∀ q ∈ U, ∀ z ∈ sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4),
        ‖hillHminusContinuedPrimitive (z^2,q)+I*(k : ℂ)*Real.pi‖ ≤ Al := D.exists_fixed_primitive_bound k
  let U (k : ℕ+) := (hfixed k).choose
  have hU (k : ℕ+) := (hfixed k).choose_spec
  let B : Fin (M+1) → Set PeriodOneHminusOne := fun i =>
    if hi : 0 < i.val then U ⟨i.val,hi⟩ else univ
  have hB (i : Fin (M+1)) : IsOpen (B i) ∧ (0 : PeriodOneHminusOne) ∈ B i := by
    by_cases hi : 0 < i.val
    · simpa only [B,dif_pos hi] using ⟨(hU ⟨i.val,hi⟩).1,(hU ⟨i.val,hi⟩).2.1⟩
    · simp only [B,dif_neg hi]
      exact ⟨isOpen_univ,mem_univ _⟩
  let W := (V ∩ (Vt ∩ Vs)) ∩ ⋂ i, B i
  refine ⟨W,Ah+Al,fun _ hq => hq.1.1,
    (D.isOpen.inter (hVt.inter hVs)).inter (isOpen_iInter_of_finite fun i => (hB i).1),
    ⟨⟨D.zero_mem,h0Vt,h0Vs⟩,mem_iInter.mpr (fun i => (hB i).2)⟩,add_pos hAh hAl,?_⟩
  intro q hq k z hz
  by_cases hk : (k : ℕ) ≤ M
  · have hi := mem_iInter.mp hq.2 (⟨(k : ℕ),Nat.lt_succ_of_le hk⟩ : Fin (M+1))
    exact ((hU k).2.2 q (by simpa only [B,dif_pos k.pos] using! hi) z hz).trans (by linarith)
  · exact (hhigh q hq.1 k (Nat.lt_of_not_ge hk).le z hz).trans (by linarith)

end HillHminusAllContourPeriodData

structure HillHminusUniformPeriodData (C : HillHminusMiuraChart) (N : ℕ)
    (V : Set PeriodOneHminusOne) (A : ℝ) : Prop extends HillHminusAllContourPeriodData C N V where
  amplitude_pos : 0 < A
  critical_close : ∀ n : ℕ+, ∀ q ∈ V,
    ‖sqrt (hillHminusUniformCriticalPoint C N n q)-(Real.pi : ℂ)*(n : ℕ)‖ < Real.pi/8
  primitive_bound : ∀ k : ℕ+, ∀ q ∈ V, ∀ z ∈ sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4),
    ‖hillHminusContinuedPrimitive (z^2,q)+I*(k : ℂ)*Real.pi‖ ≤ A

theorem exists_hillHminus_uniform_period_data :
    ∃ C : HillHminusMiuraChart, ∃ N : ℕ, ∃ V : Set PeriodOneHminusOne, ∃ A : ℝ,
      0 < N ∧ HillHminusUniformPeriodData C N V A := by
  obtain ⟨C,N,V,hN,D⟩ := exists_hillHminus_all_contour_period_data
  obtain ⟨Uc,hUcV,hUc,h0Uc,hclose⟩ := D.exists_uniform_critical_control
  obtain ⟨U,A,hUUc,hU,h0U,hA,hbound⟩ := (D.mono hUcV hUc h0Uc).exists_uniform_primitive_bound
  exact ⟨C,N,U,A,hN,⟨D.mono (hUUc.trans hUcV) hU h0U,hA,
    fun n q hq => hclose n q (hUUc hq),fun k q hq z hz => hbound q hq k z hz⟩⟩

end NLS.KdV
