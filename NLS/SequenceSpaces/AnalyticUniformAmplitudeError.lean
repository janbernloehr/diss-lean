import NLS.ComplexAnalysis.UniformAmplitudeError
import NLS.SequenceSpaces.PositiveBoundedAnalyticFamily

/-! Uniform complex squared-amplitude decay produces an analytic
weighted amplitude-error symbol, including all finite positive labels. -/
noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.Coeff

theorem exists_analytic_uniform_amplitude_error
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (V : Set E) (hV : IsOpen V) (q : E) (hqV : q∈V)
    (A : E → Coeff ⊤) (hAa : AnalyticOnNhd ℂ A V)
    (a : ℕ+ → ℝ) (ha : ∀ n,0<a n) (ha1 : ∀ n,a n≤1)
    (hpos : ∀ n : ℕ+,0<(A q (n:ℤ)).re)
    (N : ℕ) (K : ℝ) (hK : 0≤K)
    (hsq : ∀ n : ℕ+,N≤(n:ℕ) → ∀ p∈V,(1+(n:ℝ))*‖(A p (n:ℤ)/(a n:ℂ))^2-1‖≤K) :
    ∃ U : Set E,IsOpen U ∧ q∈U ∧ U⊆V ∧
      ∃ C : ℝ,∃ M : E → Coeff ⊤,0≤C ∧ AnalyticOnNhd ℂ M U ∧ ∀ p∈U,
        ‖M p‖≤C ∧ (∀ j : ℤ,j≤0 → M p j=0) ∧ ∀ n : ℕ+,
          M p (n:ℤ)=(1+(n:ℂ))*(A p (n:ℤ)-(a n:ℂ)) := by
  obtain ⟨r,hrpos,hball⟩ := Metric.mem_nhds_iff.mp (inter_mem (hV.mem_nhds hqV)
    ((hAa q hqV).continuousAt (ball_mem_nhds (A q) (by norm_num : (0:ℝ)<1))))
  let U := ball q r
  let B := ‖A q‖+1
  have hbound (p) (hp : p∈U) : ‖A p‖≤B := by
    have ht : ‖A p-A q‖<1 := by simpa only [mem_preimage,mem_ball,dist_eq_norm] using (hball hp).2
    exact (norm_le_norm_sub_add (A p) (A q)).trans (by dsimp only [B];linarith)
  have hcont (n : ℕ+) : ContinuousOn (fun p => A p (n:ℤ)) U :=
    (((lp.evalCLM ℂ (fun _ : ℤ => ℂ) ⊤ (n:ℤ)).continuous).comp_continuousOn
      (hAa.continuousOn.mono (fun p hp => (hball hp).1)))
  obtain ⟨C,hC,herr⟩ := NLS.ComplexAnalysis.exists_uniform_weighted_amplitude_error U (convex_ball q r).isPreconnected
    q (mem_ball_self hrpos) (fun n p => A p (n:ℤ)) a ha ha1 hcont hpos N K B hK
    (by dsimp only [B];positivity)
    (fun p hp n => (lp.norm_apply_le_norm (by simp : (⊤:ℝ≥0∞)≠0) (A p) (n:ℤ)).trans (hbound p hp))
    (fun p hp n hn => hsq n hn p (hball hp).1)
  let f := fun n : ℕ+ => fun p => (1+(n:ℂ))*(A p (n:ℤ)-(a n:ℂ))
  have hfa (n : ℕ+) : AnalyticOnNhd ℂ (f n) U := fun p hp => analyticAt_const.mul
    (((((lp.evalCLM ℂ (fun _ : ℤ => ℂ) ⊤ (n:ℤ)).analyticAt _).comp (hAa p (hball hp).1))).sub analyticAt_const)
  have hfb (p) (hp : p∈U) (n : ℕ+) : ‖f n p‖≤C := by
    change ‖(1+(n:ℂ))*(A p (n:ℤ)-(a n:ℂ))‖≤C
    rw [norm_mul,show ‖1+(n:ℂ)‖=1+(n:ℝ) by
      rw [←Nat.cast_one,←Nat.cast_add,Complex.norm_natCast,Nat.cast_add,Nat.cast_one]]
    exact herr p hp n
  obtain ⟨M,hMa,hM⟩ := exists_positive_bounded_analytic_lift U isOpen_ball f C hC hfa hfb
  exact ⟨U,isOpen_ball,mem_ball_self hrpos,(fun p hp => (hball hp).1),C,M,hC,hMa,hM⟩

end NLS.Coeff
