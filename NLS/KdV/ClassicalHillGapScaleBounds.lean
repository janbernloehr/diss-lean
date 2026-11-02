import NLS.KdV.ClassicalHillGapQuotients

/-! # Gap-length scale bounds for the actual high Hill primitive square

The actual endpoint-deflated quotient turns the common disc bound into
K_n=O(gamma_n^2/n^2) throughout a gap-sized disc. The actual continued
primitive obeys F_n=O(gamma_n/n) on its admissible part. Constructing the
canonical unsquared branch on the full cut complement remains separate.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.LinearVolterra NLS.ComplexAnalysis
namespace NLS.KdV

theorem norm_complex_midpoint_sub_le (l u c : ℂ) (epsilon : ℝ)
    (hl : ‖l-c‖ ≤ epsilon) (hu : ‖u-c‖ ≤ epsilon) :
    ‖(l+u)/2-c‖ ≤ epsilon := by
  rw [show (l+u)/2-c = ((l-c)+(u-c))/2 by ring,norm_div]
  norm_num
  linarith [norm_add_le (l-c) (u-c)]

theorem closed_gap_ball_subset_energy_disc (l u c : ℂ) (R : ℝ) (hR : 0 < R)
    (hl : ‖l-c‖ ≤ R/8) (hu : ‖u-c‖ ≤ R/8) :
    closedBall ((l+u)/2) ‖l-u‖ ⊆ closedBall c R := by
  have hgap : ‖l-u‖ ≤ R/4 := by
    have h := norm_sub_le_norm_sub_add_norm_sub l c u
    rw [norm_sub_rev c u] at h
    linarith
  have hmid := norm_complex_midpoint_sub_le l u c (R/8) hl hu
  intro z hz
  have hz' : ‖z-(l+u)/2‖ ≤ ‖l-u‖ := by simpa only [mem_closedBall,dist_eq_norm] using hz
  have h := norm_sub_le_norm_sub_add_norm_sub z ((l+u)/2) c
  have hzc : ‖z-c‖ ≤ R := by linarith
  simpa only [mem_closedBall,dist_eq_norm] using hzc

theorem closed_gap_ball_subset_energy_ball (l u c : ℂ) (R : ℝ) (hR : 0 < R)
    (hl : ‖l-c‖ ≤ R/8) (hu : ‖u-c‖ ≤ R/8) :
    closedBall ((l+u)/2) ‖l-u‖ ⊆ ball c R := by
  have hgap : ‖l-u‖ ≤ R/4 := by
    have h := norm_sub_le_norm_sub_add_norm_sub l c u
    rw [norm_sub_rev c u] at h
    linarith
  have hmid := norm_complex_midpoint_sub_le l u c (R/8) hl hu
  intro z hz
  have hz' : ‖z-(l+u)/2‖ ≤ ‖l-u‖ := by simpa only [mem_closedBall,dist_eq_norm] using hz
  have h := norm_sub_le_norm_sub_add_norm_sub z ((l+u)/2) c
  have hzc : ‖z-c‖ < R := by linarith
  simpa only [mem_ball,dist_eq_norm] using hzc

theorem norm_two_zero_square_on_gap_ball
    (F Q : ℂ → ℂ) (l u z : ℂ) (R : ℝ)
    (hf : F z = (z-l)*(z-u)*Q z) (hQ : ‖Q z‖ ≤ 4/R^2)
    (hz : z ∈ closedBall ((l+u)/2) ‖l-u‖) :
    ‖F z‖ ≤ 9*‖l-u‖^2/R^2 := by
  have hml : ‖(l+u)/2-l‖ = ‖l-u‖/2 := by
    rw [show (l+u)/2-l = (u-l)/2 by ring,norm_div,norm_sub_rev u l]
    norm_num
  have hmu : ‖(l+u)/2-u‖ = ‖l-u‖/2 := by
    rw [show (l+u)/2-u = (l-u)/2 by ring,norm_div]
    norm_num
  have hz' : ‖z-(l+u)/2‖ ≤ ‖l-u‖ := by simpa only [mem_closedBall,dist_eq_norm] using hz
  have hzl : ‖z-l‖ ≤ 3*‖l-u‖/2 := by
    have h := norm_sub_le_norm_sub_add_norm_sub z ((l+u)/2) l
    rw [hml] at h
    linarith
  have hzu : ‖z-u‖ ≤ 3*‖l-u‖/2 := by
    have h := norm_sub_le_norm_sub_add_norm_sub z ((l+u)/2) u
    rw [hmu] at h
    linarith
  rw [hf,norm_mul,norm_mul]
  calc
    _ ≤ (3*‖l-u‖/2)*(3*‖l-u‖/2)*(4/R^2) := by gcongr
    _ = 9*‖l-u‖^2/R^2 := by ring

theorem norm_le_gap_scale_of_square_bound (f k : ℂ) (gamma R : ℝ)
    (hgamma : 0 ≤ gamma) (hR : 0 < R) (hsq : f^2 = k)
    (hk : ‖k‖ ≤ 9*gamma^2/R^2) : ‖f‖ ≤ 3*gamma/R := by
  have h : ‖f‖^2 ≤ 9*gamma^2/R^2 := by rw [← norm_pow,hsq]; exact hk
  have he : (3*gamma/R)^2 = 9*gamma^2/R^2 := by ring
  have hn : 0 ≤ 3*gamma/R := by positivity
  nlinarith [norm_nonneg f]

/-- The cutoff, complex neighborhood and constant precede all high
indices and all actual gap pairs. The square estimate holds throughout
the full gap-sized disc, including collapsed gaps and nonadmissible
energies; the continued primitive estimate holds wherever it is defined. -/
theorem exists_classicalHill_gap_scaled_primitive_bounds (q : Curve ℂ) :
    ∃ r C : ℝ, ∃ N : ℕ, ∃ V : Set (Curve ℂ),
      0 < r ∧ 0 < C ∧ 0 < N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ n : ℕ+, N ≤ (n : ℕ) → ∃ K : ℂ × Curve ℂ → ℂ,
        AnalyticOnNhd ℂ K (classicalHillGapSquareDisc n r ×ˢ V) ∧
        ∀ a ∈ V, ∃ l u : ℂ, ClassicalHillHighGapPair a n l u ∧
          (closedBall ((l+u)/2) ‖l-u‖ ⊆ classicalHillGapSquareDisc n r) ∧
          (∀ z ∈ closedBall ((l+u)/2) ‖l-u‖,
            ‖K (z,a)‖ ≤ 9*‖l-u‖^2/(Real.pi*(n : ℕ)*r)^2) ∧
          ∀ z ∈ closedBall ((l+u)/2) ‖l-u‖,
            (z,a) ∈ classicalHillContinuationDomain →
              ‖classicalHillContinuedPrimitive (z,a)+I*(n : ℂ)*Real.pi‖ ≤ C*‖l-u‖/(n : ℕ) := by
  obtain ⟨r,N,V,hr,_,hN,hV,hq,hfamily⟩ := exists_classicalHill_gap_quotient_bounds q
  let C : ℝ := 3/(Real.pi*r)
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨r,C,N,V,hr,hC,hN,hV,hq,?_⟩
  intro n hn
  obtain ⟨K,hK,_,_,hmatch,hpairs⟩ := hfamily n hn
  refine ⟨K,hK,?_⟩
  intro a ha
  obtain ⟨l,u,hpair,hl,hu,_,hfactor,_,hbound⟩ := hpairs a ha
  let c : ℂ := ((Real.pi : ℂ)*(n : ℕ))^2
  let R : ℝ := Real.pi*(n : ℕ)*r
  have hR : 0 < R := by dsimp only [R]; positivity
  have hl' : ‖l-c‖ ≤ R/8 := (show ‖l-c‖ < R/8 by simpa only [mem_ball,dist_eq_norm] using hl).le
  have hu' : ‖u-c‖ ≤ R/8 := (show ‖u-c‖ < R/8 by simpa only [mem_ball,dist_eq_norm] using hu).le
  have hsub := closed_gap_ball_subset_energy_disc l u c R hR hl' hu'
  have hboundK (z : ℂ) (hz : z ∈ closedBall ((l+u)/2) ‖l-u‖) :
      ‖K (z,a)‖ ≤ 9*‖l-u‖^2/R^2 :=
    norm_two_zero_square_on_gap_ball (fun z => K (z,a))
      (twoZeroQuotient (fun z => K (z,a)) l u) l u z R (hfactor z) (hbound z (hsub hz)) hz
  refine ⟨l,u,hpair,hsub,hboundK,?_⟩
  intro z hz hdom
  have hsq := hmatch (z,a) ⟨⟨hsub hz,ha⟩,hdom⟩
  have hf := norm_le_gap_scale_of_square_bound _ (K (z,a)) ‖l-u‖ R (norm_nonneg _) hR
    hsq.symm (hboundK z hz)
  calc
    _ ≤ 3*‖l-u‖/R := hf
    _ = C*‖l-u‖/(n : ℕ) := by
      have hnpos : (0 : ℝ) < (n : ℕ) := by positivity
      dsimp only [C,R]
      field_simp [Real.pi_ne_zero,hr.ne',hnpos.ne']

end NLS.KdV
