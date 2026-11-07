import NLS.ComplexAnalysis.SegmentPrimitiveBoundary

/-! Full relative endpoint limits for a primitive of an analytic
numerator divided by ANY continuous root of a nondegenerate quadratic.
The estimate uses both endpoint distances, retaining the selected sheet. -/
noncomputable section
open Set Metric Complex Filter Topology
namespace NLS.ComplexAnalysis

theorem quadratic_root_ne_zero_off_segment (l r z Q : ℂ)
    (hz : z ∉ segment ℝ l r) (hsq : Q^2 = (l-z)*(r-z)) : Q ≠ 0 := by
  have hl : l ≠ z := by
    intro h
    exact hz (h ▸ left_mem_segment ℝ l r)
  have hr : r ≠ z := by
    intro h
    exact hz (h ▸ right_mem_segment ℝ l r)
  have hprod := mul_ne_zero (sub_ne_zero.mpr hl) (sub_ne_zero.mpr hr)
  intro hzero
  apply hprod
  rw [← hsq,hzero]
  simp

theorem quadratic_root_endpoint_norm_lower_bound (l r a z Q : ℂ)
    (ha : a ∈ ({l,r} : Set ℂ)) (hsq : Q^2 = (l-z)*(r-z))
    (hnear : ‖a-z‖ ≤ ‖r-l‖/2) :
    Real.sqrt ((‖r-l‖/2)*‖a-z‖) ≤ ‖Q‖ := by
  have hn : ‖Q‖^2 = ‖l-z‖*‖r-z‖ := by rw [← norm_pow,hsq,norm_mul]
  have htri : ‖r-l‖ ≤ ‖r-z‖+‖l-z‖ := by
    simpa only [sub_sub_sub_cancel_right] using norm_sub_le (r-z) (l-z)
  have hp : (‖r-l‖/2)*‖a-z‖ ≤ ‖Q‖^2 := by
    simp only [mem_insert_iff,mem_singleton_iff] at ha
    rcases ha with ha | ha
    · subst a
      have hh : ‖r-l‖/2 ≤ ‖r-z‖ := by linarith
      rw [hn]
      nlinarith [mul_le_mul_of_nonneg_right hh (norm_nonneg (l-z))]
    · subst a
      have hh : ‖r-l‖/2 ≤ ‖l-z‖ := by linarith
      rw [hn]
      exact mul_le_mul_of_nonneg_right hh (norm_nonneg (r-z))
  apply Real.sqrt_le_iff.mpr
  exact ⟨norm_nonneg _,hp⟩

theorem exists_quadratic_root_primitive_endpoint_limits (g Q F : ℂ → ℂ)
    (c l r : ℂ) (R : ℝ) (hlr : l ≠ r) (hgap : segment ℝ l r ⊆ ball c R)
    (hg : ContinuousOn g (closedBall c R))
    (hQ : ContinuousOn Q (ball c R \ segment ℝ l r))
    (hsq : ∀ z ∈ ball c R \ segment ℝ l r, Q z^2 = (l-z)*(r-z))
    (hF : ∀ z ∈ ball c R \ segment ℝ l r, HasDerivAt F (g z/Q z) z) :
    ∃ A B : ℂ, Tendsto F (𝓝[ball c R \ segment ℝ l r] l) (𝓝 A) ∧
      Tendsto F (𝓝[ball c R \ segment ℝ l r] r) (𝓝 B) := by
  obtain ⟨C,hC⟩ := (isCompact_closedBall c R).exists_bound_of_continuousOn hg
  let M : ℝ := max C 0+1
  have hM : 0 ≤ M := by dsimp [M]; positivity
  let d : ℝ := ‖r-l‖/2
  have hd : 0 < d := div_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hlr.symm)) (by norm_num)
  have hne (z : ℂ) (hz : z ∈ ball c R \ segment ℝ l r) : Q z ≠ 0 :=
    quadratic_root_ne_zero_off_segment l r z (Q z) hz.2 (hsq z hz)
  have hf : ContinuousOn (fun z => g z/Q z) (ball c R \ segment ℝ l r) :=
    (hg.mono (fun _ hz => ball_subset_closedBall hz.1)).div hQ hne
  have hb : ∀ a ∈ ({l,r} : Set ℂ), ∀ z ∈ ball c R \ segment ℝ l r, ‖z-a‖ ≤ d →
      ‖g z/Q z*(Real.sqrt (d*‖z-a‖) : ℂ)‖ ≤ M := by
    intro a ha z hz hnear
    have hw : Real.sqrt (d*‖z-a‖) ≤ ‖Q z‖ := by
      simpa only [d,norm_sub_rev] using quadratic_root_endpoint_norm_lower_bound l r a z (Q z) ha (hsq z hz)
        (by simpa only [d,norm_sub_rev] using hnear)
    have hqpos : 0 < ‖Q z‖ := norm_pos_iff.mpr (hne z hz)
    rw [norm_mul,norm_div,Complex.norm_real,Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    calc
      _ = ‖g z‖*(Real.sqrt (d*‖z-a‖)/‖Q z‖) := by ring
      _ ≤ ‖g z‖*1 := mul_le_mul_of_nonneg_left ((div_le_one hqpos).mpr hw) (norm_nonneg _)
      _ ≤ M := by
        rw [mul_one]
        exact (hC z (ball_subset_closedBall hz.1)).trans (by dsimp [M]; linarith [le_max_left C 0])
  obtain ⟨A,hA⟩ := exists_primitive_segment_left_boundary_limit _ F (ball c R) l r d M d
    isOpen_ball (hgap (left_mem_segment ℝ _ _)) hlr hd hM hd hf hF (hb l (by simp))
  obtain ⟨B,hB⟩ := exists_primitive_segment_right_boundary_limit _ F (ball c R) l r d M d
    isOpen_ball (hgap (right_mem_segment ℝ _ _)) hlr hd hM hd hf hF (hb r (by simp))
  exact ⟨A,B,hA,hB⟩

end NLS.ComplexAnalysis
