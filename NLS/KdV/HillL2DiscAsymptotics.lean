import NLS.KdV.HillL2EnergyDiscriminant
import NLS.ZakharovShabat.LocallyUniformDiscriminantAsymptotics
import NLS.ZakharovShabat.FreeCircleSeparation
import NLS.ZakharovShabat.FreeExteriorCutoffs
import NLS.ComplexAnalysis.DiscBounds
import NLS.ComplexAnalysis.ParametricSourceLogDomain
import NLS.ZakharovShabat.SourcePhysicalL2Equiv

/-! # Uniform high-disc trace approximation in the actual L2 topology

The physical constant-upper L2 system is realized inside the existing
canonical ZS discriminant by restriction and the source Fourier isometry.
The established exterior trace estimate and maximum modulus principle
therefore control whole high discs on complex L2 neighborhoods. No
continuity of the potential, individual root labels, or Birkhoff map is
assumed.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.KdV

def hillL2CoefficientPotential (q : Coeff 2) : PairSpace 2 :=
  periodOnePotential (sourcePhysicalL2Equiv.symm (physicalRestrictionL2 (hillFirstOrderPotential q)))

theorem continuous_hillL2CoefficientPotential : Continuous hillL2CoefficientPotential :=
  (periodOnePotential (p := 2)).continuous.comp (sourcePhysicalL2Equiv.symm.continuous.comp
    (physicalRestrictionL2CLM.continuous.comp (continuous_const.prodMk continuous_id.neg)))

theorem analyticOnNhd_hillL2CoefficientPotential :
    AnalyticOnNhd ℂ hillL2CoefficientPotential univ := by
  intro q _
  have hphi : AnalyticAt ℂ hillFirstOrderPotential q := analyticAt_const.prod analyticAt_id.neg
  have hu := (physicalRestrictionL2CLM.analyticAt (hillFirstOrderPotential q)).comp hphi
  have hs := (sourcePhysicalL2Equiv.symm.toContinuousLinearEquiv.analyticAt _).comp hu
  exact ((periodOnePotential (p := 2)).analyticAt _).comp hs

theorem hillL2CoefficientPotential_even (q : Coeff 2) :
    hillL2CoefficientPotential q ∈ pairParitySubspace 0 := periodOnePotential_mem _

theorem canonicalDiscriminant_hillL2CoefficientPotential (q : Coeff 2) (z : ℂ) :
    canonicalDiscriminant (by simp) (hillL2CoefficientPotential q) z =
      hillL2Discriminant q (z^2) := by
  rw [hillL2CoefficientPotential,canonicalDiscriminant_eq_l2_source,
    sourcePhysicalL2_equiv_symm,hillL2Discriminant_sq]
  rfl

theorem exists_hillL2_disc_trace_approximation
    (q : Coeff 2) (r : ℝ) (hr : 0 < r) (hrpi : r ≤ Real.pi/4)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ N : ℕ, ∃ V : Set (Coeff 2), 0 < N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ a ∈ V, ∀ n : ℤ, N ≤ n.natAbs → ∀ z ∈ closedBall ((Real.pi : ℂ)*n) r,
        ‖hillL2Discriminant a (z^2)-2*cos z‖ ≤ epsilon := by
  obtain ⟨U,hU,_,hq,_,R,hbound⟩ := exists_uniform_discriminant_error_exp
    (by simp : (2 : ℝ≥0∞) ≠ ⊤) (by norm_num : 1 < (2 : ℝ≥0∞))
    (hillL2CoefficientPotential q) hr hrpi
    (by positivity : 0 < epsilon/Real.exp r)
  obtain ⟨N,hN,hNR⟩ := exists_free_center_cutoff R r
  refine ⟨N,hillL2CoefficientPotential ⁻¹' U,hN,
    hU.preimage continuous_hillL2CoefficientPotential,hq,?_⟩
  intro a ha n hn z hz
  have hf : Differentiable ℂ (fun w =>
      canonicalDiscriminant (by simp) (hillL2CoefficientPotential a) w-freeDiscriminant w) := by
    intro w
    exact (analyticOnNhd_canonicalDiscriminant (by simp) (by norm_num)
      (hillL2CoefficientPotential a) (hillL2CoefficientPotential_even a) w
      (mem_univ _)).differentiableAt.sub (hasDerivAt_freeDiscriminant w).differentiableAt
  have hc (w : ℂ) (hw : w ∈ sphere ((Real.pi : ℂ)*n) r) :
      ‖canonicalDiscriminant (by simp) (hillL2CoefficientPotential a) w-freeDiscriminant w‖ ≤ epsilon := by
    have hb := hbound _ ha (hillL2CoefficientPotential_even a) w
      (norm_ge_of_mem_freeSphere hNR hn hw) (freeCircle_separated r (by linarith) n w hw)
    calc
      _ ≤ epsilon/Real.exp r*Real.exp |w.im| := hb
      _ ≤ epsilon/Real.exp r*Real.exp r := mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (freeCircle_im_le r n w hw)) (by positivity)
      _ = epsilon := div_mul_cancel₀ epsilon (Real.exp_ne_zero r)
  have hm := norm_le_of_sphere_bound hf ((Real.pi : ℂ)*n) hr epsilon hc
    (by simpa only [mem_closedBall,dist_eq_norm] using hz)
  rw [canonicalDiscriminant_hillL2CoefficientPotential] at hm
  exact hm

/-- Compact subsets admit one complex L2 neighborhood and one cutoff,
before every high index and every point of its full disc. -/
theorem exists_hillL2_disc_trace_approximation_near_compact
    (K : Set (Coeff 2)) (hK : IsCompact K)
    (r : ℝ) (hr : 0 < r) (hrpi : r ≤ Real.pi/4) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ N : ℕ, ∃ V : Set (Coeff 2), 0 < N ∧ IsOpen V ∧ K ⊆ V ∧
      ∀ a ∈ V, ∀ n : ℤ, N ≤ n.natAbs → ∀ z ∈ closedBall ((Real.pi : ℂ)*n) r,
        ‖hillL2Discriminant a (z^2)-2*cos z‖ ≤ epsilon := by
  classical
  have hl (q : K) := exists_hillL2_disc_trace_approximation q.val r hr hrpi epsilon hepsilon
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

/-- Uniform approximation along all straight source paths in a complex
L2 neighborhood. The affine first-order realization need not preserve zero. -/
theorem exists_hillL2_source_disc_trace_approximation
    (q : Coeff 2) (r : ℝ) (hr : 0 < r) (hrpi : r ≤ Real.pi/4)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ N : ℕ, ∃ V : Set (Coeff 2), 0 < N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ a ∈ V, ∀ s ∈ Icc (0 : ℝ) 1, ∀ n : ℤ, N ≤ n.natAbs →
        ∀ z ∈ closedBall ((Real.pi : ℂ)*n) r,
          ‖hillL2Discriminant ((s : ℂ) • a) (z^2)-2*cos z‖ ≤ epsilon := by
  let K : Set (Coeff 2) := (fun s : ℝ => (s : ℂ) • q) '' Icc (0 : ℝ) 1
  have hK : IsCompact K := isCompact_Icc.image (by fun_prop)
  obtain ⟨N,U,hN,hU,hKU,hd⟩ :=
    exists_hillL2_disc_trace_approximation_near_compact K hK r hr hrpi epsilon hepsilon
  let D : Set (ℂ × Coeff 2) := univ ×ˢ U
  let V : Set (Coeff 2) := (fun a => ((0 : ℂ),a)) ⁻¹' sourceSegmentDomain 0 D
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
