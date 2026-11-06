import NLS.SequenceSpaces.PositiveBoundedAnalyticFamily

/-! # Uniform lower bounds and actual reciprocals of positive symbols -/
noncomputable section
set_option autoImplicit false
open Set Metric Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {E : Type*} [NormedAddCommGroup E]

/-- A native infinity symbol with a positive lower bound at one base
retains a common lower bound on ONE complex neighborhood of that base. -/
theorem exists_local_positive_symbol_lower
    (U : Set E) (hU : IsOpen U) (M : E → Coeff ⊤) (q : E) (hq : q∈U)
    (hc : ContinuousAt M q) (a : ℝ) (ha : 0<a)
    (hl : ∀ n : ℕ+, a≤‖M q (n : ℤ)‖) :
    ∃ V : Set E, IsOpen V ∧ q∈V ∧ V⊆U ∧ ∀ p∈V, ∀ n : ℕ+, a/2≤‖M p (n : ℤ)‖ := by
  obtain ⟨W,hWV,hW,hqW⟩ := _root_.mem_nhds_iff.mp
    (inter_mem (hU.mem_nhds hq) (hc (isOpen_ball.mem_nhds (mem_ball_self (by positivity : 0<a/2)))))
  refine ⟨W,hW,hqW,fun p hp => (hWV hp).1,?_⟩
  intro p hp n
  have hd : ‖M p-M q‖<a/2 := by simpa only [mem_preimage,mem_ball,dist_eq_norm] using (hWV hp).2
  have hn := lp.norm_apply_le_norm (by simp : (⊤ : ℝ≥0∞)≠0) (M p-M q) (n : ℤ)
  have ht : ‖M q (n : ℤ)‖≤‖M p (n : ℤ)-M q (n : ℤ)‖+‖M p (n : ℤ)‖ := by
    calc
      _ = ‖(M q (n : ℤ)-M p (n : ℤ))+M p (n : ℤ)‖ := by rw [sub_add_cancel]
      _ ≤ _ := by simpa only [norm_sub_rev] using norm_add_le (M q (n : ℤ)-M p (n : ℤ)) (M p (n : ℤ))
  change ‖M p (n : ℤ)-M q (n : ℤ)‖≤‖M p-M q‖ at hn
  linarith [hl n]

variable [NormedSpace ℂ E]

/-- Positive slots bounded away from zero have an ACTUAL native analytic
reciprocal symbol, with zero nonpositive slots and an exact product one. -/
theorem exists_positive_analytic_reciprocal
    (U : Set E) (hU : IsOpen U) (M : E → Coeff ⊤)
    (hM : AnalyticOnNhd ℂ M U) (a : ℝ) (ha : 0<a)
    (hl : ∀ p∈U, ∀ n : ℕ+, a≤‖M p (n : ℤ)‖) :
    ∃ N : E → Coeff ⊤, AnalyticOnNhd ℂ N U ∧ ∀ p∈U,
      ‖N p‖≤a⁻¹ ∧ (∀ j : ℤ, j≤0 → N p j=0) ∧ ∀ n : ℕ+,
        N p (n : ℤ)=(M p (n : ℤ))⁻¹ ∧ M p (n : ℤ)*N p (n : ℤ)=1 := by
  have hn (p : E) (hp : p∈U) (n : ℕ+) : M p (n : ℤ)≠0 :=
    norm_pos_iff.mp (ha.trans_le (hl p hp n))
  obtain ⟨N,hNa,hNd⟩ := exists_positive_bounded_analytic_lift U hU
    (fun n p => (M p (n : ℤ))⁻¹) a⁻¹ (by positivity) (by
      intro n p hp
      exact (((lp.evalCLM ℂ (fun _ : ℤ => ℂ) ⊤ (n : ℤ)).analyticAt (M p)).comp (hM p hp)).inv (hn p hp n)) (by
      intro p hp n
      rw [norm_inv]
      simpa only [one_div] using one_div_le_one_div_of_le ha (hl p hp n))
  refine ⟨N,hNa,?_⟩
  intro p hp
  refine ⟨(hNd p hp).1,(hNd p hp).2.1,?_⟩
  intro n
  exact ⟨(hNd p hp).2.2 n,by rw [(hNd p hp).2.2 n,mul_inv_cancel₀ (hn p hp n)]⟩

end NLS.Coeff
