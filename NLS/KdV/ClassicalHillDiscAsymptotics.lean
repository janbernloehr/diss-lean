import NLS.KdV.ClassicalContourCoverage
import NLS.ZakharovShabat.LocallyUniformDiscriminantAsymptotics
import NLS.ZakharovShabat.FreeCircleSeparation
import NLS.ZakharovShabat.FreeExteriorCutoffs
import NLS.ComplexAnalysis.DiscBounds

/-! # Uniform free trace approximation on entire high Hill discs

The physical constant-upper Fourier comparison transfers the established
locally uniform exterior trace asymptotic. The maximum-modulus principle
extends it from high circles to their complete discs, including their
actual branch points. Compactness yields common complex potential
neighborhoods and cutoffs, also along all straight source paths.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.KdV

/-- The actual energy trace approaches its free frequency trace uniformly
on complete high discs and on one complex neighborhood of any potential. -/
theorem exists_classicalHill_disc_trace_approximation
    (q : Curve ℂ) (r : ℝ) (hr : 0 < r) (hrpi : r ≤ Real.pi/4)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ N : ℕ, ∃ V : Set (Curve ℂ), 0 < N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ a ∈ V, ∀ n : ℤ, N ≤ n.natAbs → ∀ z ∈ closedBall ((Real.pi : ℂ)*n) r,
        ‖classicalHillDiscriminant a (z^2)-2*cos z‖ ≤ epsilon := by
  obtain ⟨U,hU,_,hq,_,R,hbound⟩ := exists_uniform_discriminant_error_exp
    (by simp : (2 : ℝ≥0∞) ≠ ⊤) (by norm_num : 1 < (2 : ℝ≥0∞))
    (classicalHillCoefficientPotential q) hr hrpi
    (by positivity : 0 < epsilon/Real.exp r)
  obtain ⟨N,hN,hNR⟩ := exists_free_center_cutoff R r
  refine ⟨N,classicalHillCoefficientPotential ⁻¹' U,hN,
    hU.preimage continuous_classicalHillCoefficientPotential,hq,?_⟩
  intro a ha n hn z hz
  have hf : Differentiable ℂ (fun w =>
      canonicalDiscriminant (by simp) (classicalHillCoefficientPotential a) w-freeDiscriminant w) := by
    intro w
    exact (analyticOnNhd_canonicalDiscriminant (by simp) (by norm_num)
      (classicalHillCoefficientPotential a) (classicalHillCoefficientPotential_even a) w
      (mem_univ _)).differentiableAt.sub (hasDerivAt_freeDiscriminant w).differentiableAt
  have hc (w : ℂ) (hw : w ∈ sphere ((Real.pi : ℂ)*n) r) :
      ‖canonicalDiscriminant (by simp) (classicalHillCoefficientPotential a) w-freeDiscriminant w‖
        ≤ epsilon := by
    have hb := hbound _ ha (classicalHillCoefficientPotential_even a) w
      (norm_ge_of_mem_freeSphere hNR hn hw) (freeCircle_separated r (by linarith) n w hw)
    calc
      _ ≤ epsilon/Real.exp r*Real.exp |w.im| := hb
      _ ≤ epsilon/Real.exp r*Real.exp r := mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (freeCircle_im_le r n w hw)) (by positivity)
      _ = epsilon := div_mul_cancel₀ epsilon (Real.exp_ne_zero r)
  have hm := norm_le_of_sphere_bound hf ((Real.pi : ℂ)*n) hr epsilon hc
    (by simpa only [mem_closedBall,dist_eq_norm] using hz)
  rw [classicalHillDiscriminant_sq,← canonicalDiscriminant_classicalHillCoefficientPotential]
  exact hm

/-- One cutoff and complex neighborhood work near a whole compact set
of continuous potentials, before every high index and every disc point. -/
theorem exists_classicalHill_disc_trace_approximation_near_compact
    (K : Set (Curve ℂ)) (hK : IsCompact K)
    (r : ℝ) (hr : 0 < r) (hrpi : r ≤ Real.pi/4) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ N : ℕ, ∃ V : Set (Curve ℂ), 0 < N ∧ IsOpen V ∧ K ⊆ V ∧
      ∀ a ∈ V, ∀ n : ℤ, N ≤ n.natAbs → ∀ z ∈ closedBall ((Real.pi : ℂ)*n) r,
        ‖classicalHillDiscriminant a (z^2)-2*cos z‖ ≤ epsilon := by
  classical
  have hl (q : K) := exists_classicalHill_disc_trace_approximation q.val r hr hrpi epsilon hepsilon
  choose N V hN hV hqV hd using hl
  obtain ⟨S,hS⟩ := hK.elim_finite_subcover V hV
    (fun q hq => mem_iUnion.mpr ⟨⟨q,hq⟩,hqV ⟨q,hq⟩⟩)
  refine ⟨1+∑ q ∈ S, N q,⋃ q ∈ S, V q,by omega,
    isOpen_iUnion (fun q => isOpen_iUnion (fun _ => hV q)),hS,?_⟩
  intro a ha n hn z hz
  obtain ⟨q,hq⟩ := mem_iUnion.mp ha
  obtain ⟨hqS,haV⟩ := mem_iUnion.mp hq
  have hNq : N q ≤ ∑ b ∈ S, N b := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hqS
  exact hd q a haV n (by omega) z hz

/-- Uniform free approximation on every complete high disc along all
source paths of nearby complex potentials. The source segment is compact;
it is not assumed that the physical affine Fourier map sends zero to zero. -/
theorem exists_classicalHill_source_disc_trace_approximation
    (q : Curve ℂ) (r : ℝ) (hr : 0 < r) (hrpi : r ≤ Real.pi/4)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ N : ℕ, ∃ V : Set (Curve ℂ), 0 < N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ a ∈ V, ∀ s ∈ Icc (0 : ℝ) 1, ∀ n : ℤ, N ≤ n.natAbs →
        ∀ z ∈ closedBall ((Real.pi : ℂ)*n) r,
          ‖classicalHillDiscriminant ((s : ℂ) • a) (z^2)-2*cos z‖ ≤ epsilon := by
  let K : Set (Curve ℂ) := (fun s : ℝ => (s : ℂ) • q) '' Icc (0 : ℝ) 1
  have hK : IsCompact K := isCompact_Icc.image (by fun_prop)
  obtain ⟨N,U,hN,hU,hKU,hd⟩ :=
    exists_classicalHill_disc_trace_approximation_near_compact K hK r hr hrpi epsilon hepsilon
  let D : Set (ℂ × Curve ℂ) := univ ×ˢ U
  let V : Set (Curve ℂ) := (fun a => ((0 : ℂ),a)) ⁻¹' sourceSegmentDomain 0 D
  have hV : IsOpen V := (isOpen_sourceSegmentDomain 0 D (isOpen_univ.prod hU)).preimage
    (continuous_const.prodMk continuous_id)
  have hqV : q ∈ V := by
    intro s hs
    exact ⟨mem_univ _,by simpa only [sourceSegmentMap,zero_add,sub_zero] using hKU ⟨s,hs,rfl⟩⟩
  refine ⟨N,V,hN,hV,hqV,?_⟩
  intro a ha s hs n hn z hz
  have haU : (s : ℂ) • a ∈ U := by
    simpa only [sourceSegmentMap,zero_add,sub_zero] using (ha s hs).2
  exact hd _ haU n hn z hz

end NLS.KdV
