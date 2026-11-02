import NLS.KdV.ClassicalHillMomentCutRoot
import NLS.ComplexAnalysis.AnalyticCutContour

/-! # Quartic gap bounds for the actual high Hill cubic moments

Shrink the analytic cut-root energy circle to the gap-length circle.
Its radius contributes one gap factor, and the cubed primitive contributes
three more. Collapsed pairs use the constructed root's analytic extension.
All estimates hold on one common complex potential neighborhood.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.LinearVolterra NLS.ComplexAnalysis
namespace NLS.KdV

theorem norm_cubicMoment_cut_le_gap
    (B : ℂ → ℂ) (c l u : ℂ) (R A m : ℝ)
    (hR : 0 < R)
    (hl : l ∈ ball c (R/8)) (hu : u ∈ ball c (R/8))
    (hB : AnalyticOnNhd ℂ B (ball c R \ segment ℝ l u))
    (hcollapsed : l = u → AnalyticOnNhd ℂ B (ball c R))
    (hbound : ∀ z ∈ closedBall ((l+u)/2) ‖l-u‖ \ segment ℝ l u,
      ‖B z‖ ≤ A*‖l-u‖/m) :
    ‖cubicMoment B c (R/2)‖ ≤ 2*A^3*‖l-u‖^4/m^3 := by
  have houter : closedBall c (R/2) ⊆ ball c R :=
    closedBall_subset_ball (by linarith)
  by_cases he : l = u
  · have hzero := cubicMoment_eq_zero_of_analyticOnNhd B c (R/2) (by positivity)
      ((hcollapsed he).mono houter)
    simp only [hzero,norm_zero,he,sub_self,norm_zero,zero_pow (by norm_num : 4 ≠ 0),mul_zero,zero_div,le_refl]
  have hgamma : 0 < ‖l-u‖ := norm_pos_iff.mpr (sub_ne_zero.mpr he)
  have hl' : ‖l-c‖ < R/8 := by simpa only [mem_ball,dist_eq_norm] using hl
  have hu' : ‖u-c‖ < R/8 := by simpa only [mem_ball,dist_eq_norm] using hu
  have hgap : ‖l-u‖ ≤ R/4 := by
    have hh := norm_sub_le_norm_sub_add_norm_sub l c u
    rw [norm_sub_rev c u] at hh
    linarith
  have hmid := norm_complex_midpoint_sub_le l u c (R/8) hl'.le hu'.le
  have hnest : closedBall ((l+u)/2) ‖l-u‖ ⊆ closedBall c (R/2) := by
    intro z hz
    have hz' : ‖z-(l+u)/2‖ ≤ ‖l-u‖ := by simpa only [mem_closedBall,dist_eq_norm] using hz
    have hh := norm_sub_le_norm_sub_add_norm_sub z ((l+u)/2) c
    have hh' : ‖z-c‖ ≤ R/2 := by linarith
    simpa only [mem_closedBall,dist_eq_norm] using hh'
  have hseginner : segment ℝ l u ⊆ ball ((l+u)/2) ‖l-u‖ := by
    apply (convex_ball _ _).segment_subset
    · rw [mem_ball,dist_eq_norm,show l-(l+u)/2 = (l-u)/2 by ring,norm_div]
      norm_num
      exact sub_ne_zero.mpr he
    · rw [mem_ball,dist_eq_norm,show u-(l+u)/2 = (u-l)/2 by ring,norm_div,norm_sub_rev u l]
      norm_num
      exact sub_ne_zero.mpr he
  have hsegouter : segment ℝ l u ⊆ ball c (R/2) := (convex_ball _ _).segment_subset
    (ball_subset_ball (by linarith : R/8 ≤ R/2) hl)
    (ball_subset_ball (by linarith : R/8 ≤ R/2) hu)
  have heq := circleIntegral_eq_of_analytic_cut_nestedCircles (fun z => B z^3)
    (ball c R) (segment ℝ l u) (hB.pow 3) ((l+u)/2) c ‖l-u‖ (R/2)
    hgamma (by positivity) hseginner hsegouter hnest houter
  have hmoment : cubicMoment B c (R/2) = cubicMoment B ((l+u)/2) ‖l-u‖ :=
    congrArg (fun z : ℂ => (Real.pi : ℂ)⁻¹*z) heq.symm
  have hb := norm_cubicMoment_le B ((l+u)/2) ‖l-u‖ (A*‖l-u‖/m) hgamma.le (by
    intro z hz
    have hznot : z ∉ segment ℝ l u := by
      intro hh
      have hzlt : ‖z-(l+u)/2‖ < ‖l-u‖ := by simpa only [mem_ball,dist_eq_norm] using hseginner hh
      have hzeq : ‖z-(l+u)/2‖ = ‖l-u‖ := by simpa only [mem_sphere,dist_eq_norm] using hz
      linarith
    exact hbound z ⟨sphere_subset_closedBall hz,hznot⟩)
  rw [hmoment]
  calc
    _ ≤ 2*‖l-u‖*(A*‖l-u‖/m)^3 := hb
    _ = 2*A^3*‖l-u‖^4/m^3 := by ring

/-- The moment is the literal original energy-contour moment, with its
free normalization, indexed shift, factor 1/pi and frequency Jacobian.
The constant, cutoff and complex neighborhood precede every tail index
and potential. Actual double roots are included. -/
theorem exists_classicalHill_high_cubic_gap_bounds (q : Curve ℂ) :
    ∃ C : ℝ, ∃ N : ℕ, ∃ V : Set (Curve ℂ),
      0 < C ∧ 0 < N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ n : ℕ+, N ≤ (n : ℕ) → ∀ a ∈ V,
        ∃ l u : ℂ, ClassicalHillHighGapPair a n l u ∧
          ‖classicalHillHighContourMoment n a‖ ≤ C*‖l-u‖^4/(n : ℕ)^3 := by
  obtain ⟨r,A,Nk,Vk,hr,hrpi,hA,hNk,hVk,hqk,hfamily⟩ := exists_classicalHill_gap_cut_roots q
  obtain ⟨Nm,Vm,hNm,hVm,hqm,hcover,hmoments⟩ :=
    exists_classicalHill_high_moment_radius_independence q (r/4) (by positivity) (by linarith)
  let N := max Nk Nm
  let V := Vk ∩ Vm
  refine ⟨2*A^3,N,V,by positivity,hNk.trans_le (le_max_left _ _),hVk.inter hVm,⟨hqk,hqm⟩,?_⟩
  intro n hn a ha
  have hnk : Nk ≤ (n : ℕ) := (le_max_left Nk Nm).trans hn
  have hnm : Nm ≤ (n : ℕ) := (le_max_right Nk Nm).trans hn
  obtain ⟨K,_,hmatch,hpairs⟩ := hfamily n hnk
  obtain ⟨l,u,B,hpair,hl,hu,_,hB,hsq,hcollapsed,hbound⟩ := hpairs a ha.1
  obtain ⟨k,hk,hM⟩ := classicalHill_moment_eq_signed_cut_moment a n r (fun z => K (z,a)) B l u
    hr hrpi hl hu hB hsq
    (fun z hz hdom => hmatch (z,a) ⟨⟨hz,ha.1⟩,hdom⟩)
    (fun z hz => hcover a ha.2 n hnm z
      (closedBall_subset_closedBall (by linarith : r/4 ≤ Real.pi/4) (sphere_subset_closedBall hz)) (by
        have hh : ‖z-(Real.pi : ℂ)*(n : ℕ)‖ = r/4 := by simpa only [mem_sphere,dist_eq_norm] using hz
        exact hh.ge))
    (hmoments a ha.2 n hnm (r/4) ⟨le_rfl,by linarith⟩)
  have hR : 0 < Real.pi*(n : ℕ)*r := by positivity
  have hb := norm_cubicMoment_cut_le_gap B (((Real.pi : ℂ)*(n : ℕ))^2) l u
    (Real.pi*(n : ℕ)*r) A (n : ℕ) hR hl hu hB hcollapsed hbound
  refine ⟨l,u,hpair,?_⟩
  rw [hM,norm_mul,norm_pow]
  rcases hk with rfl | rfl <;> simpa using hb

/-- The exact summand weight from the renormalized Hamiltonian leaves
the square of the gap/action scale. The remaining action comparison is
not assumed to be a property of an arbitrary coordinate map. -/
theorem exists_classicalHill_high_weighted_cubic_gap_bounds (q : Curve ℂ) :
    ∃ C : ℝ, ∃ N : ℕ, ∃ V : Set (Curve ℂ),
      0 < C ∧ 0 < N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ n : ℕ+, N ≤ (n : ℕ) → ∀ a ∈ V,
        ∃ l u : ℂ, ClassicalHillHighGapPair a n l u ∧
          ‖((8*(n : ℕ)*Real.pi : ℝ) : ℂ)*classicalHillHighContourMoment n a‖ ≤
            C*(‖l-u‖^2/(n : ℕ))^2 := by
  obtain ⟨C,N,V,hC,hN,hV,hq,hbound⟩ := exists_classicalHill_high_cubic_gap_bounds q
  refine ⟨8*Real.pi*C,N,V,by positivity,hN,hV,hq,?_⟩
  intro n hn a ha
  obtain ⟨l,u,hpair,hb⟩ := hbound n hn a ha
  have hnpos : (0 : ℝ) < (n : ℕ) := by positivity
  refine ⟨l,u,hpair,?_⟩
  rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (by positivity)]
  calc
    _ ≤ (8*(n : ℕ)*Real.pi)*(C*‖l-u‖^4/(n : ℕ)^3) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = (8*Real.pi*C)*(‖l-u‖^2/(n : ℕ))^2 := by
      field_simp [hnpos.ne']

/-- The literal moments are analytic and satisfy their weighted gap
estimate on the same complex neighborhood and with one common cutoff. -/
theorem exists_analytic_classicalHill_moments_with_gap_bounds (q : Curve ℂ) :
    ∃ C : ℝ, ∃ N : ℕ, ∃ V : Set (Curve ℂ),
      0 < C ∧ 0 < N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ n : ℕ+, N ≤ (n : ℕ) →
        AnalyticOnNhd ℂ (classicalHillHighContourMoment n) V ∧
        ∀ a ∈ V, ∃ l u : ℂ, ClassicalHillHighGapPair a n l u ∧
          ‖((8*(n : ℕ)*Real.pi : ℝ) : ℂ)*classicalHillHighContourMoment n a‖ ≤
            C*(‖l-u‖^2/(n : ℕ))^2 := by
  obtain ⟨C,Nb,Vb,hC,hNb,hVb,hqb,hbound⟩ := exists_classicalHill_high_weighted_cubic_gap_bounds q
  obtain ⟨Na,Va,_,hVa,hqa,hanalytic⟩ := exists_analytic_classicalHillHighContourMoments q
  refine ⟨C,max Nb (Na+1),Vb ∩ Va,hC,hNb.trans_le (le_max_left _ _),hVb.inter hVa,
    ⟨hqb,hqa⟩,?_⟩
  intro n hn
  have hnb : Nb ≤ (n : ℕ) := (le_max_left Nb (Na+1)).trans hn
  have hna : Na < (n : ℕ) := by have := (le_max_right Nb (Na+1)).trans hn; omega
  exact ⟨(hanalytic n hna).mono inter_subset_right,fun a ha => hbound n hnb a ha.1⟩

end NLS.KdV
