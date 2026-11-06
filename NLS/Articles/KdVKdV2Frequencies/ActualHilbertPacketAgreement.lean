import NLS.Articles.KdVKdV2Frequencies.ActualWeakHilbertKdVFrequencyPacket
import NLS.Articles.KdVKdV2Frequencies.ActualHilbertWeakFrequencyAgreement

/-! # The bounded actual weak-frequency packet and global physical Hilbert map

The genuine weighted ell2 weak-action extension and the genuine
Hilbert gradient are the SAME correction on a full complex intersection.
Both domains precede all modes and the Hilbert domain retains its ENTIRE
nonnegative cone. The weak domain remains local at zero; full global weak
extension, sharper lp remainders below exponent two and compactness remain separate obligations. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.KdV NLS.ZakharovShabat NLS.Articles.KdVConvexity
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

theorem exists_actual_hilbert_packet_frequency_agreement
    (D : GlobalRoughAbelianForwardData) :
    ∃ ρ K : ℝ, ∃ g : Coeff 1 → Coeff 2, ∃ E : PhysicalHstarExtension, ∃ V : Set ActionSpace,
      0<ρ ∧ 0<K ∧ IsOpen V ∧ positiveQuadrant⊆V ∧ V⊆E.domain ∧
      AnalyticOnNhd ℂ g (ball (0 : Coeff 1) ρ) ∧
      (∀ a∈ball (0 : Coeff 1) ρ, ‖g a‖≤K ∧ ∀ j : ℤ, j≤0 → g a j=0) ∧
      (∀ a∈ball (0 : Coeff 1) ρ, a∈Coeff.nonnegativeLocus 1 → ∀ j : ℤ, (g a j).im=0) ∧
      AnalyticOnNhd ℂ (actionGradient E.hamiltonian) V ∧
      (∀ a∈positiveQuadrant, ∀ n, (actionGradient E.hamiltonian a n).im=0) ∧
      actionGradient E.hamiltonian 0=0 ∧
      fderiv ℂ (actionGradient E.hamiltonian) 0=(-6 : ℂ) • ContinuousLinearMap.id ℂ ActionSpace ∧
      (∀ a∈V, hilbertWeakActions a∈ball (0 : Coeff 1) ρ → ∀ n : ℕ+,
        g (hilbertWeakActions a) (n : ℤ)=actionGradient E.hamiltonian a n/(n : ℂ)) ∧
      (∀ a : WeightedCoeff.positiveActionLocus (Weight.sobolev 3) 1, ∀ n,
        actionGradient E.hamiltonian (originalActionInclusion (physicalHilbertActionReindex a.val)) n=
          (D.originalKdVFrequency a n : ℂ)-((2*Real.pi*(n : ℝ))^3 : ℝ)) ∧
      ∀ q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1 : ℕ) : ℝ)),
        D.nativeWeakActionSequence 1 q∈ball (0 : Coeff 1) ρ → ∀ n : ℕ+,
          g (D.nativeWeakActionSequence 1 q) (n : ℤ)=
            ((D.nativeSourceHierarchyFrequency 1 3 (by norm_num) q n : ℂ)-(2*(n : ℂ)*Real.pi)^3)/(n : ℂ) := by
  obtain ⟨r,K,g,hr,hK,hg,hbound,hreal,hrec⟩ := D.exists_actual_weak_hilbert_kdv_frequency_packet
  let E := Classical.choice nonempty_physicalHstarExtension
  have hcone : Convex ℝ positiveQuadrant := by
    intro a ha b hb u v hu hv _ n
    change (u • a n+v • b n).im=0 ∧ 0≤(u • a n+v • b n).re
    constructor
    · simp [(ha n).1,(hb n).1]
    · simpa using add_nonneg (mul_nonneg hu (ha n).2) (mul_nonneg hv (hb n).2)
  obtain ⟨V,hV,hconeV,hVE,hcommon⟩ :=
    NLS.ComplexAnalysis.exists_open_cone_weak_component_neighborhood hilbertWeakActions
      positiveQuadrant E.domain hcone zero_mem_positiveQuadrant E.isOpen E.contains_cone r hr
  have hsub : ball (0 : Coeff 1) (r/2)⊆ball (0 : Coeff 1) r := ball_subset_ball (by linarith)
  let f : ℕ+ → Coeff 1 → ℂ := fun n a => (n : ℂ)*g a (n : ℤ)
  have hf (n : ℕ+) : AnalyticOnNhd ℂ (f n) (ball (0 : Coeff 1) r) := by
    intro a ha
    exact analyticAt_const.mul (((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 (n : ℤ)).analyticAt _).comp (hg a ha))
  have hfrecover (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1 : ℕ) : ℝ)))
      (hq : D.nativeWeakActionSequence 1 q∈ball (0 : Coeff 1) r) (n : ℕ+) :
      f n (D.nativeWeakActionSequence 1 q)=
        (D.nativeSourceHierarchyFrequency 1 3 (by norm_num) q n : ℂ)-(2*(n : ℂ)*Real.pi)^3 := by
    change (n : ℂ)*g (D.nativeWeakActionSequence 1 q) (n : ℤ)=_
    rw [hrec q hq n]
    have hn : (n : ℂ)≠0 := by exact_mod_cast n.pos.ne'
    field_simp
  have ht := E.Taylor_at_zero
  refine ⟨r/2,K,g,E,V,by positivity,hK,hV,hconeV,hVE,hg.mono hsub,
    (fun a ha => hbound a (hsub ha)),(fun a ha => hreal a (hsub ha)),
    (analyticOnNhd_actionGradient _ E.analytic).mono hVE,
    (fun a ha n => D.physicalHilbertGradient_real E a ha n),ht.2.1,ht.2.2,?_,
    (fun a n => (D.originalKdVFrequency_correction_eq_gradient E a n).symm),
    (fun q hq n => hrec q (hsub hq) n)⟩
  intro a ha hweak n
  let U := E.domain∩hilbertWeakActions ⁻¹' ball (0 : Coeff 1) r
  let W := connectedComponentIn U (0 : ActionSpace)
  have hWsub : W⊆U := connectedComponentIn_subset U 0
  have hfa : AnalyticOnNhd ℂ (fun b : ActionSpace => f n (hilbertWeakActions b)) W :=
    fun b hb => (hf n _ (hWsub hb).2).comp (hilbertWeakActions.analyticAt b)
  have hG : AnalyticOnNhd ℂ (fun b : ActionSpace => actionGradient E.hamiltonian b n) W :=
    fun b hb => ((lp.evalCLM ℂ (fun _ : ℕ+ => ℂ) 2 n).analyticAt _).comp
      (analyticOnNhd_actionGradient _ E.analytic b (hWsub hb).1)
  have h0W : (0 : ActionSpace)∈W := mem_connectedComponentIn
    ⟨E.contains_cone zero_mem_positiveQuadrant,by
      change hilbertWeakActions (0 : ActionSpace)∈ball (0 : Coeff 1) r
      rw [map_zero]
      exact mem_ball_self hr⟩
  have he := hfa.eqOn_of_preconnected_of_eventuallyEq hG isPreconnected_connectedComponentIn h0W
    (D.weakFrequency_eventuallyEq_HilbertGradient_zero E r hr f hf hfrecover n)
      (hcommon ⟨ha,hweak⟩)
  have hn : (n : ℂ)≠0 := by exact_mod_cast n.pos.ne'
  apply (eq_div_iff hn).mpr
  exact (mul_comm _ _).trans he

/-- The SAME genuine weighted weak packet vanishes at zero and obeys a
linear Banach norm bound on ONE smaller complex weak-action ball. Thus the
ACTUAL native correction is bounded by L*n*norm(Aweak), before all modes. -/
theorem exists_actual_weak_hilbert_kdv_frequency_linear_bound (D : GlobalRoughAbelianForwardData) :
    ∃ ρ L : ℝ, ∃ g : Coeff 1 → Coeff 2,
      0<ρ ∧ 0<L ∧ AnalyticOnNhd ℂ g (ball (0 : Coeff 1) ρ) ∧ g 0=0 ∧
      (∀ a∈ball (0 : Coeff 1) ρ, ‖g a‖≤L*‖a‖ ∧ ∀ j : ℤ, j≤0 → g a j=0) ∧
      (∀ a∈ball (0 : Coeff 1) ρ, a∈Coeff.nonnegativeLocus 1 → ∀ j : ℤ, (g a j).im=0) ∧
      ∀ q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1 : ℕ) : ℝ)),
        D.nativeWeakActionSequence 1 q∈ball (0 : Coeff 1) ρ → ∀ n : ℕ+,
          g (D.nativeWeakActionSequence 1 q) (n : ℤ)=
            ((D.nativeSourceHierarchyFrequency 1 3 (by norm_num) q n : ℂ)-(2*(n : ℂ)*Real.pi)^3)/(n : ℂ) ∧
          ‖(D.nativeSourceHierarchyFrequency 1 3 (by norm_num) q n : ℂ)-(2*(n : ℂ)*Real.pi)^3‖≤
            L*(n : ℝ)*‖D.nativeWeakActionSequence 1 q‖ := by
  obtain ⟨r,K,g,E,V,hr,_hK,_hV,hcone,_hVE,hg,hbound,hreal,_hGa,_hGreal,hG0,_hDG,hagree,_hphys,hrec⟩ :=
    D.exists_actual_hilbert_packet_frequency_agreement
  have hzero : g (0 : Coeff 1)=0 := by
    ext j
    by_cases hj : 0<j
    · let n := positiveIntegerIndex j hj
      have hnj : (n : ℤ)=j := positiveIntegerIndex_int j hj
      have h0weak : hilbertWeakActions (0 : ActionSpace)∈ball (0 : Coeff 1) r := by
        rw [map_zero];exact mem_ball_self hr
      have he := hagree 0 (hcone zero_mem_positiveQuadrant) h0weak n
      rw [map_zero,hG0] at he
      rw [←hnj,he]
      simp only [lp.coeFn_zero,Pi.zero_apply,zero_div]
    · rw [(hbound 0 (mem_ball_self hr)).2 j (by omega)]
      rfl
  have hO := (hg 0 (mem_ball_self hr)).differentiableAt.isBigO_sub
  obtain ⟨L,hL,hOL⟩ := hO.exists_pos
  have hevent : ∀ᶠ a : Coeff 1 in 𝓝 0, ‖g a‖≤L*‖a‖ := by
    simpa only [hzero,sub_zero] using hOL.bound
  obtain ⟨ε,hε,hεball⟩ := Metric.mem_nhds_iff.mp hevent
  let ρ := min r ε
  have hρ : 0<ρ := lt_min hr hε
  have hsub : ball (0 : Coeff 1) ρ⊆ball 0 r := ball_subset_ball (min_le_left _ _)
  have hlinear (a : Coeff 1) (ha : a∈ball (0 : Coeff 1) ρ) : ‖g a‖≤L*‖a‖ :=
    hεball (ball_subset_ball (min_le_right _ _) ha)
  refine ⟨ρ,L,g,hρ,hL,hg.mono hsub,hzero,
    (fun a ha => ⟨hlinear a ha,(hbound a (hsub ha)).2⟩),
    (fun a ha => hreal a (hsub ha)),?_⟩
  intro q hq n
  refine ⟨hrec q (hsub hq) n,?_⟩
  have hn : (0 : ℝ)<n := by positivity
  have hc := (lp.norm_apply_le_norm (by simp : (2 : ENNReal)≠0)
    (g (D.nativeWeakActionSequence 1 q)) (n : ℤ)).trans (hlinear _ hq)
  rw [hrec q (hsub hq) n,norm_div,Complex.norm_natCast] at hc
  exact ((div_le_iff₀ hn).mp hc).trans_eq (by ring)

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
