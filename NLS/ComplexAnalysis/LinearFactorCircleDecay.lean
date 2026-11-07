import NLS.ComplexAnalysis.DiscBounds

/-! Transfer of circle decay through a filled linear-factor identity.
No division at the finite factor zero or analytic hypothesis is needed. -/
noncomputable section
open Set Metric Complex Filter Topology
namespace NLS.ComplexAnalysis

theorem linearFactor_circle_decay (F G S : ℂ → ℂ) (a b : ℂ) (R : ℕ → ℝ)
    (hR : Tendsto R atTop atTop) (hfill : ∀ z, (b+z)*F z = a*G z)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ k, K ≤ k →
      ∀ z ∈ sphere (0:ℂ) (R k), ‖G z/S z‖ ≤ ε) :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ k, K ≤ k →
      ∀ z ∈ sphere (0:ℂ) (R k), ‖F z/S z‖ ≤ ε := by
  intro ε hε
  have hb : 0 < ‖a‖+1 := by positivity
  obtain ⟨K,hK⟩ := hsmall (ε/(‖a‖+1)) (div_pos hε hb)
  obtain ⟨L,hL⟩ := eventually_atTop.mp (hR.eventually_ge_atTop (‖b‖+1))
  refine ⟨max K L,?_⟩
  intro k hk z hz
  have hnorm : ‖z‖ = R k := by simpa only [mem_sphere,dist_zero_right] using hz
  have htri := norm_le_norm_sub_add z (-b)
  simp only [sub_neg_eq_add,norm_neg] at htri
  have hden : 1 ≤ ‖b+z‖ := by rw [add_comm b] ; linarith [hL k ((le_max_right K L).trans hk)]
  have hne : b+z ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) hden)
  have he : F z/S z = (a/(b+z))*(G z/S z) := by
    have hf : F z = a*G z/(b+z) := (eq_div_iff hne).mpr (by rw [mul_comm]; exact hfill z)
    rw [hf]
    ring
  rw [he,norm_mul,norm_div]
  calc
    _ ≤ ‖a‖*(ε/(‖a‖+1)) := mul_le_mul (div_le_self (norm_nonneg _) hden)
      (hK k ((le_max_left K L).trans hk) z hz) (norm_nonneg _) (norm_nonneg _)
    _ ≤ ε := by rw [← mul_div_assoc]; apply (div_le_iff₀ hb).mpr; nlinarith

end NLS.ComplexAnalysis
