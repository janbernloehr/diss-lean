import NLS.KdV.HillHminusLocalActionAmplitude
import NLS.KdV.HillFreeDeflatedTraceSlope
import NLS.ComplexAnalysis.CollapsedQuadraticSolutionValue

/-! # Actual free-normalized quadratic primitive germs in the rough source norm -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
namespace NLS.KdV
variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

def hillCenteredFreeTrace (n : ℕ+) (t : ℂ × PeriodOneHminusOne) : ℂ :=
  hillHminusLocalDeflatedTrace h0q h0r n
    (hillHminusLocalGapMidpoint h0q h0r n t.2+t.1,t.2)

theorem analyticAt_hillCenteredFreeTrace_zero (n : ℕ+) :
    AnalyticAt ℂ (hillCenteredFreeTrace h0q h0r n) (0,0) := by
  obtain ⟨V,_hV,h0V,hM,_hS⟩ := exists_hillHminusLocalGapMoments_analytic h0q h0r n
  have hτ : AnalyticAt ℂ (fun t : ℂ × PeriodOneHminusOne =>
      hillHminusLocalGapMidpoint h0q h0r n t.2) (0,0) :=
    AnalyticAt.comp (x := ((0 : ℂ),(0 : PeriodOneHminusOne)))
      (g := hillHminusLocalGapMidpoint h0q h0r n)
      (f := fun t : ℂ × PeriodOneHminusOne => t.2) (hM 0 h0V) analyticAt_snd
  have hT := (hτ.add analyticAt_fst).prod analyticAt_snd
  apply (analyticAt_hillHminusLocalDeflatedTrace_zero h0q h0r n).comp_of_eq hT
  change (hillHminusLocalGapMidpoint h0q h0r n 0+0,(0 : PeriodOneHminusOne))=_
  rw [(hillHminusLocalGapMoments_zero h0q h0r n).1,add_zero]

theorem deriv_hillCenteredFreeTrace_zero (n : ℕ+) :
    deriv (fun w => hillCenteredFreeTrace h0q h0r n (w,0)) 0 = I/(2*(n : ℂ)*Real.pi) := by
  let c : ℂ := hillRealGapCenter 0 h0q h0r (n : ℕ)
  obtain ⟨E,V,hE,_hV,hgap,h0V,hmatch⟩ :=
    exists_hillLocalDeflatedTraceNumerator_physical_neighborhood 0 h0q h0r (n : ℕ) n.property
  have hcE : c ∈ E := by
    apply hgap
    have hc : hillRealGapCenter 0 h0q h0r (n : ℕ)=hillRealLabels 0 h0q h0r (2*(n : ℕ)-1) := by
      exact (hillFreeGapCenter h0q h0r (n : ℕ) n.property).trans
        (hillFreeGapEndpoints h0q h0r (n : ℕ) n.property).1.symm
    rw [show c=(hillRealLabels 0 h0q h0r (2*(n : ℕ)-1) : ℂ) by rw [←hc]]
    exact left_mem_segment ℝ _ _
  have ht : Tendsto (fun w : ℂ => c+w) (𝓝 0) (𝓝 c) := by
    simpa using! ((continuous_const (y := c)).add continuous_id).tendsto (0 : ℂ)
  have he : (fun w => hillCenteredFreeTrace h0q h0r n (w,0)) =ᶠ[𝓝 0]
      (fun w => hillDeflatedTraceNumerator 0 h0q h0r (n : ℕ) (c+w)) := by
    filter_upwards [ht.eventually (hE.mem_nhds hcE)] with w hw
    rw [hillCenteredFreeTrace,(hillHminusLocalGapMoments_zero h0q h0r n).1]
    have hL := hillHminusLocalDeflatedTrace_l2 h0q h0r n (0 : Coeff 2) (c+w)
    simp only [map_zero] at hL
    have hm0 : hillLocalDeflatedTraceNumerator 0 h0q h0r (n : ℕ) (c+w,0)=
        hillDeflatedTraceNumerator 0 h0q h0r (n : ℕ) (c+w) := by
      simpa only [map_zero] using! (hmatch ⟨0,h0q,h0r⟩ h0V (c+w) hw).2.2
    exact hL.trans hm0
  have hcfill : c ∈ hillGapFilledDomain 0 h0q h0r (n : ℕ) := (hmatch ⟨0,h0q,h0r⟩ h0V c hcE).2.1
  have hline : HasDerivAt (fun w : ℂ => c+w) 1 0 := by
    simpa only [id_eq] using (hasDerivAt_id (0 : ℂ)).const_add c
  have hd : HasDerivAt (fun w : ℂ => hillDeflatedTraceNumerator 0 h0q h0r (n : ℕ) (c+w))
      (deriv (hillDeflatedTraceNumerator 0 h0q h0r (n : ℕ)) c) 0 := by
    simpa only [add_zero,mul_one] using!
      ((analyticOnNhd_hillDeflatedTraceNumerator 0 h0q h0r (n : ℕ) n.property c hcfill).differentiableAt.hasDerivAt).comp_of_eq
        0 hline (by simp)
  rw [he.deriv_eq,hd.deriv]
  dsimp only [c]
  exact (congrArg (fun x : ℝ => deriv (hillDeflatedTraceNumerator 0 h0q h0r (n : ℕ)) (x : ℂ))
    (hillFreeGapCenter h0q h0r (n : ℕ) n.property)).trans
      (deriv_hillDeflatedTraceNumerator_free h0q h0r (n : ℕ) n.property)

/-- The actual trace and symmetric rough gap data construct an analytic
root amplitude. Its value at the free collapsed gap is fixed exactly,
with no unspecified sign or normalizing constant. The centered cosine
mean is retained explicitly until its physical zero-period identification. -/
theorem exists_hillFree_quadratic_primitive_germ (n : ℕ+) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ V : Set PeriodOneHminusOne, IsOpen V ∧ 0 ∈ V ∧
      ∃ Q : ℂ × PeriodOneHminusOne → ℂ,
        AnalyticOnNhd ℂ Q (ball (0 : ℂ) ρ ×ˢ V) ∧
        Q (0,0)=I/(2*(n : ℂ)*Real.pi) ∧
        ∀ p ∈ V, ‖sqrt (hillHminusLocalGapSquare h0q h0r n p/4)‖ < ρ ∧
          ∀ w ∈ ball (0 : ℂ) ρ,
            (w^2-hillHminusLocalGapSquare h0q h0r n p/4)*deriv (fun z => Q (z,p)) w+w*Q (w,p) =
              centeredMeanFree (hillCenteredFreeTrace h0q h0r n)
                (fun q => hillHminusLocalGapSquare h0q h0r n q/4) (w,p) := by
  let s : PeriodOneHminusOne → ℂ := fun p => hillHminusLocalGapSquare h0q h0r n p/4
  obtain ⟨U,_hU,h0U,_hM,hS⟩ := exists_hillHminusLocalGapMoments_analytic h0q h0r n
  have hs0 : s 0=0 := by
    dsimp only [s]
    rw [(hillHminusLocalGapMoments_zero h0q h0r n).2,zero_div]
  obtain ⟨ρ,hρ,V,hV,h0V,Q,hQ,hsol⟩ := exists_analytic_centered_mean_free_quadratic_solution
    (hillCenteredFreeTrace h0q h0r n) s 0 (analyticAt_hillCenteredFreeTrace_zero h0q h0r n)
    ((hS 0 h0U).div_const) hs0
  have hQa : AnalyticAt ℂ (fun w => Q (w,0)) 0 :=
    (hQ (0,0) ⟨mem_ball_self hρ,h0V⟩).comp
      (f := fun w : ℂ => (w,(0 : PeriodOneHminusOne))) (analyticAt_id.prod analyticAt_const)
  have he : (fun w => w^2*deriv (fun z => Q (z,0)) w+w*Q (w,0)) =ᶠ[𝓝 0]
      (fun w => hillCenteredFreeTrace h0q h0r n (w,0)-hillCenteredFreeTrace h0q h0r n (0,0)) := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hρ : (0 : ℂ) ∈ ball 0 ρ)] with w hw
    have hh := (hsol 0 h0V).2 w hw
    have hm : parametricCosineMean (hillCenteredFreeTrace h0q h0r n) (fun _ => 0)
        (sqrt (s 0),0)/(Real.pi : ℂ)=hillCenteredFreeTrace h0q h0r n (0,0) := by
      simp [hs0,parametricCosineMean,Complex.real_smul,Real.pi_ne_zero]
    rw [hs0] at hm
    simpa only [quadraticRootPolynomial,sub_zero,hs0,centeredMeanFree,hm] using hh
  have hQ0 := quadratic_solution_value_at_collapse (fun w => Q (w,0))
    (fun w => hillCenteredFreeTrace h0q h0r n (w,0)) hQa
    ((analyticAt_hillCenteredFreeTrace_zero h0q h0r n).comp
      (f := fun w : ℂ => (w,(0 : PeriodOneHminusOne)))
      (analyticAt_id.prod analyticAt_const)).differentiableAt he
  refine ⟨ρ,hρ,V,hV,h0V,Q,hQ,hQ0.trans (deriv_hillCenteredFreeTrace_zero h0q h0r n),?_⟩
  intro p hp
  exact ⟨(hsol p hp).1,fun w hw => by simpa only [quadraticRootPolynomial,sub_zero] using (hsol p hp).2 w hw⟩

end NLS.KdV
