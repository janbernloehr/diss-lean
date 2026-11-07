import NLS.ComplexAnalysis.EntireRootReplacement

/-! Replacing one energy zero preserves sub-comparison growth of the
exact quadratic differential lift. The ratio is bounded only on the
large circles where its denominator is nonzero; the filled replacement
is entire at every finite energy. -/
noncomputable section
open Set Metric Complex Filter Topology
namespace NLS.ComplexAnalysis

theorem quadratic_rootReplacement_ratio_bound (a b c z : ℂ)
    (hz : ‖c+a‖+‖b-a‖+1 ≤ ‖z‖^2) :
    z^2-c ≠ a ∧ ‖((z^2-c-b)/(z^2-c-a))‖ ≤ 2 := by
  have htri : ‖z‖^2 ≤ ‖z^2-c-a‖+‖c+a‖ := by
    calc
      ‖z‖^2 = ‖z^2‖ := (norm_pow z 2).symm
      _ = ‖(z^2-c-a)+(c+a)‖ := by congr 1; ring
      _ ≤ ‖z^2-c-a‖+‖c+a‖ := norm_add_le _ _
  have hlow : ‖b-a‖+1 ≤ ‖z^2-c-a‖ := by linarith
  have hpos : 0 < ‖z^2-c-a‖ := by linarith [norm_nonneg (b-a)]
  have hnum : ‖z^2-c-b‖ ≤ ‖z^2-c-a‖+‖b-a‖ := by
    calc
      ‖z^2-c-b‖ = ‖(z^2-c-a)+(a-b)‖ := by congr 1; ring
      _ ≤ ‖z^2-c-a‖+‖a-b‖ := norm_add_le _ _
      _ = ‖z^2-c-a‖+‖b-a‖ := by rw [norm_sub_rev a b]
  refine ⟨sub_ne_zero.mp (norm_pos_iff.mp hpos),?_⟩
  rw [norm_div]
  apply (div_le_iff₀ hpos).mpr
  linarith

theorem rootReplacement_quadratic_weight_decay
    (f : ℂ → ℂ) (a b c : ℂ) (w : ℂ → ℂ) (R : ℕ → ℝ)
    (hR : Tendsto R atTop atTop) (ha : f a = 0)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      ∀ z ∈ sphere (0:ℂ) (R k), ‖(2*z*f (z^2-c))/w z‖ ≤ ε) :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      ∀ z ∈ sphere (0:ℂ) (R k), ‖(2*z*rootReplacement f a b (z^2-c))/w z‖ ≤ ε := by
  intro ε hε
  obtain ⟨Kf,hKf⟩ := hsmall (ε/2) (by positivity)
  obtain ⟨Kr,hKr⟩ := eventually_atTop.mp (hR.eventually_ge_atTop (‖c+a‖+‖b-a‖+2))
  refine ⟨max Kf Kr,?_⟩
  intro k hk z hz
  have hnorm : ‖z‖ = R k := by simpa only [mem_sphere,dist_zero_right] using hz
  have hlarge : ‖c+a‖+‖b-a‖+2 ≤ ‖z‖ := by
    rw [hnorm]
    exact hKr k ((le_max_right _ _).trans hk)
  have hsq : ‖c+a‖+‖b-a‖+1 ≤ ‖z‖^2 := by
    nlinarith [norm_nonneg (c+a),norm_nonneg (b-a)]
  obtain ⟨hne,hbound⟩ := quadratic_rootReplacement_ratio_bound a b c z hsq
  have he : (2*z*rootReplacement f a b (z^2-c))/w z =
      ((z^2-c-b)/(z^2-c-a))*((2*z*f (z^2-c))/w z) := by
    rw [rootReplacement_eq_ratio f a b _ ha hne]
    ring
  rw [he,norm_mul]
  calc
    ‖(z^2-c-b)/(z^2-c-a)‖*‖(2*z*f (z^2-c))/w z‖ ≤ 2*(ε/2) :=
      mul_le_mul hbound (hKf k ((le_max_left _ _).trans hk) z hz) (norm_nonneg _) (by norm_num)
    _ = ε := by ring

end NLS.ComplexAnalysis
