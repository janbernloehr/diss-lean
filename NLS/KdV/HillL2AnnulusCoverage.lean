import NLS.KdV.HillL2SmallGapCoverage
import NLS.KdV.HillL2SourcePrimitive
import NLS.KdV.ClassicalHillWholeGapSquares

/-! # Common complex L2 source domains on complete high annuli

Uniform root confinement along all straight source paths gives actual
primitive coverage on entire high-frequency annuli, with no parity or
reality restriction on the complex L2 input.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV

theorem exists_hillL2_small_gap_coverage_near_compact
    (K : Set (Coeff 2)) (hK : IsCompact K)
    (r : ℝ) (hr : 0 < r) (hrpi : r ≤ Real.pi/4) :
    ∃ N : ℕ, ∃ V : Set (Coeff 2), 0 < N ∧ IsOpen V ∧ K ⊆ V ∧
      ∀ a ∈ V, ∀ n : ℤ, N ≤ n.natAbs →
        ∀ z ∈ closedBall ((Real.pi : ℂ)*n) (Real.pi/4),
          hillL2Radicand a (z^2) = 0 → z ∈ ball ((Real.pi : ℂ)*n) r := by
  classical
  have hl (q : K) := exists_hillL2_small_gap_coverage q.val r hr hrpi
  choose N V hN hV hqV hd using hl
  obtain ⟨S,hS⟩ := hK.elim_finite_subcover V hV
    (fun q hq => mem_iUnion.mpr ⟨⟨q,hq⟩,hqV ⟨q,hq⟩⟩)
  refine ⟨1+∑ q ∈ S, N q,⋃ q ∈ S, V q,by omega,
    isOpen_iUnion (fun q => isOpen_iUnion (fun _ => hV q)),hS,?_⟩
  intro a ha n hn z hz hzero
  obtain ⟨q,hq⟩ := mem_iUnion.mp ha
  obtain ⟨hqS,haV⟩ := mem_iUnion.mp hq
  have hNq : N q ≤ ∑ b ∈ S, N b := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hqS
  exact hd q a haV n (by omega) z hz hzero

theorem exists_hillL2_source_small_gap_coverage
    (q : Coeff 2) (r : ℝ) (hr : 0 < r) (hrpi : r ≤ Real.pi/4) :
    ∃ N : ℕ, ∃ V : Set (Coeff 2), 0 < N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ a ∈ V, ∀ s ∈ Icc (0 : ℝ) 1, ∀ n : ℤ, N ≤ n.natAbs →
        ∀ z ∈ closedBall ((Real.pi : ℂ)*n) (Real.pi/4),
          hillL2Radicand ((s : ℂ) • a) (z^2) = 0 → z ∈ ball ((Real.pi : ℂ)*n) r := by
  let K : Set (Coeff 2) := (fun s : ℝ => (s : ℂ) • q) '' Icc (0 : ℝ) 1
  have hK : IsCompact K := isCompact_Icc.image (by fun_prop)
  obtain ⟨N,U,hN,hU,hKU,hd⟩ :=
    exists_hillL2_small_gap_coverage_near_compact K hK r hr hrpi
  let D : Set (ℂ × Coeff 2) := univ ×ˢ U
  let V : Set (Coeff 2) := (fun a => ((0 : ℂ),a)) ⁻¹' sourceSegmentDomain 0 D
  have hV : IsOpen V := (isOpen_sourceSegmentDomain 0 D (isOpen_univ.prod hU)).preimage
    (continuous_const.prodMk continuous_id)
  have hqV : q ∈ V := by
    intro s hs
    exact ⟨mem_univ _,by simpa only [sourceSegmentMap,zero_add,sub_zero] using hKU ⟨s,hs,rfl⟩⟩
  refine ⟨N,V,hN,hV,hqV,?_⟩
  intro a ha s hs n hn z hz hzero
  have haU : (s : ℂ) • a ∈ U := by
    simpa only [sourceSegmentMap,zero_add,sub_zero] using (ha s hs).2
  exact hd _ haU n hn z hz hzero

/-- An arbitrary prescribed positive inner radius works, with one
complex neighborhood and cutoff before all potentials, indices and points. -/
theorem exists_hillL2_high_annulus_neighborhood
    (q : Coeff 2) (r : ℝ) (hr : 0 < r) (hrpi : r ≤ Real.pi/4) :
    ∃ N : ℕ, ∃ V : Set (Coeff 2), 0 < N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ a ∈ V, ∀ n : ℕ+, N ≤ (n : ℕ) →
        ∀ z ∈ closedBall ((Real.pi : ℂ)*(n : ℕ)) (Real.pi/4),
          r ≤ ‖z-(Real.pi : ℂ)*(n : ℕ)‖ → (z^2,a) ∈ hillL2ContinuationDomain := by
  obtain ⟨N,V,hN,hV,hq,hsmall⟩ := exists_hillL2_source_small_gap_coverage q r hr hrpi
  refine ⟨N,V,hN,hV,hq,?_⟩
  intro a ha n hn z hz hfar
  rw [mem_hillL2ContinuationDomain_iff]
  refine ⟨sq_mem_slitPlane_of_high_closedBall n n.property z hz,?_⟩
  intro s hs
  have hne : hillL2Radicand ((s : ℂ) • a) (z^2) ≠ 0 := by
    intro he
    have hh := hsmall a ha s hs (n : ℤ) (by simpa only [Int.natAbs_natCast] using hn) z
      (by simpa only [Int.cast_natCast] using hz) he
    have hh' : ‖z-(Real.pi : ℂ)*(n : ℕ)‖ < r := by
      simpa only [mem_ball,dist_eq_norm,Int.cast_natCast] using hh
    linarith
  exact hne

/-- A positive fixed fraction of the radius-n energy disc may be
removed. The entire remaining shell is covered on one complex L2
neighborhood, before all high indices and all shell points. -/
theorem exists_hillL2_high_energy_annulus_neighborhood
    (q : Coeff 2) (rho : ℝ) (hrho : 0 < rho) (hrho1 : rho ≤ 1) :
    ∃ N : ℕ, ∃ V : Set (Coeff 2), 0 < N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ a ∈ V, ∀ n : ℕ+, N ≤ (n : ℕ) →
        ∀ z ∈ closedBall (freeHillValue (n : ℕ) : ℂ) (n : ℝ),
          rho*(n : ℝ) ≤ ‖z-(freeHillValue (n : ℕ) : ℂ)‖ →
            (z,a) ∈ hillL2ContinuationDomain := by
  have hr : 0 < rho/(4*Real.pi) := by positivity
  have hrpi : rho/(4*Real.pi) ≤ Real.pi/4 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4*Real.pi)).mpr
    nlinarith [Real.pi_gt_three]
  obtain ⟨N,V,hN,hV,hq,hcover⟩ := exists_hillL2_high_annulus_neighborhood q _ hr hrpi
  refine ⟨N,V,hN,hV,hq,?_⟩
  intro a ha n hn z hz hfar
  let c : ℝ := Real.pi*(n : ℕ)
  have hnpos : (0 : ℝ) < (n : ℕ) := by positivity
  have hn1 : (1 : ℝ) ≤ (n : ℕ) := by exact_mod_cast n.property
  have hc : 0 < c := by dsimp only [c]; positivity
  have hcenter : (c : ℂ)^2 = (freeHillValue (n : ℕ) : ℂ) := by
    dsimp only [c,freeHillValue]
    push_cast
    ring
  have hrad : c*(1/Real.pi) = (n : ℝ) := by dsimp only [c]; field_simp
  have hsqrt := sqrt_mem_closedBall_of_energy_disc c (1/Real.pi) hc z
    (by simpa only [hcenter,hrad] using hz)
  have hnorm : ‖Complex.sqrt z-(c : ℂ)‖ ≤ 1/Real.pi := by
    simpa only [mem_closedBall,dist_eq_norm] using hsqrt
  have hquarter : 1/Real.pi ≤ Real.pi/4 := by
    apply (div_le_iff₀ Real.pi_pos).mpr
    nlinarith [Real.pi_gt_three]
  have hboundc : 1/Real.pi ≤ c := by
    apply (div_le_iff₀ Real.pi_pos).mpr
    dsimp only [c]
    nlinarith [Real.pi_gt_three]
  have hsum : ‖Complex.sqrt z+(c : ℂ)‖ ≤ 3*c := by
    have htwo : ‖(2 : ℂ)*(c : ℂ)‖ = 2*c := by simp [abs_of_pos hc]
    calc
      _ = ‖(Complex.sqrt z-(c : ℂ))+(2 : ℂ)*(c : ℂ)‖ := by congr 1; ring
      _ ≤ ‖Complex.sqrt z-(c : ℂ)‖+2*c := by
        simpa only [htwo] using norm_add_le (Complex.sqrt z-(c : ℂ)) ((2 : ℂ)*(c : ℂ))
      _ ≤ 3*c := by linarith
  have hfactor : ‖z-(c : ℂ)^2‖ = ‖Complex.sqrt z-(c : ℂ)‖*‖Complex.sqrt z+(c : ℂ)‖ := by
    rw [← norm_mul]
    congr 1
    linear_combination -(complex_sqrt_sq z)
  have hfar' : rho/(4*Real.pi) ≤ ‖Complex.sqrt z-(c : ℂ)‖ := by
    by_contra hnot
    have hsmall := mul_lt_mul_of_pos_right (not_le.mp hnot) (by positivity : 0 < 3*c)
    have he : rho/(4*Real.pi)*(3*c) = (3/4)*(rho*(n : ℝ)) := by
      dsimp only [c]
      field_simp
    rw [he] at hsmall
    rw [← hcenter,hfactor] at hfar
    have hprod := mul_le_mul_of_nonneg_left hsum (norm_nonneg (Complex.sqrt z-(c : ℂ)))
    nlinarith [mul_pos hrho hnpos]
  have hsource := hcover a ha n hn (Complex.sqrt z)
    (by
      have hs := closedBall_subset_closedBall hquarter hsqrt
      simpa only [c,ofReal_mul,ofReal_natCast] using hs)
    (by simpa only [c,ofReal_mul,ofReal_natCast] using hfar')
  simpa only [complex_sqrt_sq] using hsource

end NLS.KdV
