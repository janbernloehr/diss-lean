import NLS.KdV.HillHminusOneDiscriminant
import NLS.KdV.HillFreeEnergyShift
import NLS.ZakharovShabat.LocallyUniformDiscriminantAsymptotics
import NLS.ZakharovShabat.FreeCircleSeparation
import NLS.ZakharovShabat.FreeExteriorCutoffs
import NLS.ComplexAnalysis.DiscBounds
import NLS.ComplexAnalysis.ParametricSourceLogDomain

/-! # Uniform full high-disc trace approximation in complex H^-1

On a fixed Miura chart, the actual H^-1 Hill trace is the diagonal L2
NLS trace at sqrt(z²+c). The fixed energy translation becomes uniformly
small at high frequency. Exterior NLS estimates control each boundary,
and maximum modulus fills the complete frequency disc. Compactness then
gives common neighborhoods and cutoffs for every straight source path.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.KdV

theorem exists_hillHminus_chart_disc_trace_approximation
    (C : HillHminusMiuraChart) (q : PeriodOneHminusOne) (hq : q ∈ C.domain)
    (r : ℝ) (hr : 0 < r) (hrpi : r ≤ Real.pi/4) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ N : ℕ, ∃ V : Set PeriodOneHminusOne, 0 < N ∧ IsOpen V ∧ q ∈ V ∧ V ⊆ C.domain ∧
      ∀ a ∈ V, ∀ n : ℕ, N ≤ n → ∀ z ∈ closedBall ((Real.pi : ℂ)*n) r,
        ‖hillHminusDiscriminant a (z^2)-2*cos z‖ ≤ epsilon := by
  let psi : PeriodOneHminusOne → PairSpace 2 := fun a =>
    periodOnePotential (hillMiuraDiagonal (C.lift a))
  have hpsi : AnalyticOnNhd ℂ psi C.domain := by
    intro a ha
    exact ((periodOnePotential (p := 2)).analyticAt _).comp
      ((hillMiuraDiagonal.analyticAt _).comp (C.lift_analytic a ha))
  obtain ⟨U,hU,_,hqU,_,R,hbound⟩ := exists_uniform_discriminant_error_exp
    (by simp : (2 : ℝ≥0∞) ≠ ⊤) (by norm_num : 1 < (2 : ℝ≥0∞)) (psi q)
    (half_pos hr) (by linarith : r/2 ≤ Real.pi/4)
    (by positivity : 0 < (epsilon/2)/Real.exp (r+1))
  obtain ⟨N0,hN0,hNR⟩ := exists_free_center_cutoff (R+1) r
  obtain ⟨N1,hN1,hshift⟩ := exists_high_disc_sqrt_shift_small C.energyShift r (min 1 (r/2))
    (lt_min zero_lt_one (half_pos hr))
  obtain ⟨N2,hN2,hfree⟩ := exists_high_disc_free_trace_shift_small C.energyShift r (epsilon/2)
    (half_pos hepsilon)
  let N := 1+N0+N1+N2
  let V := C.domain ∩ psi ⁻¹' U
  have hV : IsOpen V := hpsi.continuousOn.isOpen_inter_preimage C.domain_open hU
  refine ⟨N,V,by dsimp [N]; omega,hV,⟨hq,hqU⟩,inter_subset_left,?_⟩
  intro a ha n hn z hz
  have hn0 : N0 ≤ n := by dsimp [N] at hn; omega
  have hn1 : N1 ≤ n := by dsimp [N] at hn; omega
  have hn2 : N2 ≤ n := by dsimp [N] at hn; omega
  have hf : Differentiable ℂ (fun w => hillHminusDiscriminant a (w^2)-2*cos w) := by
    intro w
    have hd := (analyticOnNhd_hillHminusDiscriminant_joint (w^2,a) (mem_univ _)).comp
      (f := fun t : ℂ => (t^2,a)) ((analyticAt_id.pow 2).prod analyticAt_const)
    have hcos : AnalyticAt ℂ (fun t : ℂ => (2 : ℂ)*cos t) w :=
      analyticAt_const.mul Complex.analyticAt_cos
    exact hd.differentiableAt.sub hcos.differentiableAt
  have hc (v : ℂ) (hv : v ∈ sphere ((Real.pi : ℂ)*n) r) :
      ‖hillHminusDiscriminant a (v^2)-2*cos v‖ ≤ epsilon := by
    let w := sqrt (v^2+C.energyShift)
    have hvInt : v ∈ sphere ((Real.pi : ℂ)*(n : ℤ)) r := by
      simpa only [Int.cast_natCast] using hv
    have hvBall : v ∈ closedBall ((Real.pi : ℂ)*n) r := sphere_subset_closedBall hv
    have hclose : ‖w-v‖ < min 1 (r/2) := (hshift n hn1 v hvBall).2
    have hclose1 : ‖w-v‖ < 1 := hclose.trans_le (min_le_left _ _)
    have hcloser : ‖w-v‖ < r/2 := hclose.trans_le (min_le_right _ _)
    have hvR : R+1 ≤ ‖v‖ := norm_ge_of_mem_freeSphere hNR
      (by simpa only [Int.natAbs_natCast] using hn0) hvInt
    have hwR : R ≤ ‖w‖ := by
      have ht := norm_le_norm_sub_add v w
      rw [norm_sub_rev v w] at ht
      linarith
    have hsep : ∀ m : ℤ, r/2 ≤ ‖w-(Real.pi : ℂ)*m‖ := by
      intro m
      have hvsep := freeCircle_separated r (by linarith) (n : ℤ) v hvInt m
      have ht := norm_sub_le_norm_sub_add_norm_sub v w ((Real.pi : ℂ)*m)
      rw [norm_sub_rev v w] at ht
      linarith
    have him : |w.im| ≤ r+1 := by
      have hvim := freeCircle_im_le r (n : ℤ) v hvInt
      have hdiff := abs_im_le_norm (w-v)
      rw [sub_im] at hdiff
      have ht := abs_add_le (w-v).im v.im
      rw [sub_im,sub_add_cancel] at ht
      linarith
    have hNLS := hbound (psi a) ha.2 (periodOnePotential_mem _) w hwR hsep
    have herror : ‖canonicalDiscriminant (by simp) (psi a) w-2*cos w‖ ≤ epsilon/2 := by
      calc
        _ ≤ (epsilon/2)/Real.exp (r+1)*Real.exp |w.im| := hNLS
        _ ≤ (epsilon/2)/Real.exp (r+1)*Real.exp (r+1) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr him) (by positivity)
        _ = epsilon/2 := div_mul_cancel₀ _ (Real.exp_ne_zero _)
    have htrace : hillHminusDiscriminant a (v^2) = canonicalDiscriminant (by simp) (psi a) w := by
      rw [hillHminusDiscriminant_eq_chart C a ha.1]
      rfl
    rw [htrace]
    have hfree' : ‖2*cos w-2*cos v‖ < epsilon/2 := hfree n hn2 v hvBall
    calc
      _ ≤ ‖canonicalDiscriminant (by simp) (psi a) w-2*cos w‖+‖2*cos w-2*cos v‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ epsilon := by linarith
  exact norm_le_of_sphere_bound hf ((Real.pi : ℂ)*n) hr epsilon hc
    (by simpa only [mem_closedBall,dist_eq_norm] using hz)

/-- A single complex H^-1 neighborhood controls every sufficiently high full disc. -/
theorem exists_hillHminus_disc_trace_approximation
    (q : PeriodOneHminusOne) (r : ℝ) (hr : 0 < r) (hrpi : r ≤ Real.pi/4)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ N : ℕ, ∃ V : Set PeriodOneHminusOne, 0 < N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ a ∈ V, ∀ n : ℕ, N ≤ n → ∀ z ∈ closedBall ((Real.pi : ℂ)*n) r,
        ‖hillHminusDiscriminant a (z^2)-2*cos z‖ ≤ epsilon := by
  obtain ⟨N,V,hN,hV,hq,_,hd⟩ := exists_hillHminus_chart_disc_trace_approximation
    (hillHminusMiuraChartAt q) q (mem_hillHminusMiuraChartAt q) r hr hrpi epsilon hepsilon
  exact ⟨N,V,hN,hV,hq,hd⟩

/-- Compact sets have one ambient complex H^-1 neighborhood and one common cutoff. -/
theorem exists_hillHminus_disc_trace_approximation_near_compact
    (K : Set PeriodOneHminusOne) (hK : IsCompact K)
    (r : ℝ) (hr : 0 < r) (hrpi : r ≤ Real.pi/4) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ N : ℕ, ∃ V : Set PeriodOneHminusOne, 0 < N ∧ IsOpen V ∧ K ⊆ V ∧
      ∀ a ∈ V, ∀ n : ℕ, N ≤ n → ∀ z ∈ closedBall ((Real.pi : ℂ)*n) r,
        ‖hillHminusDiscriminant a (z^2)-2*cos z‖ ≤ epsilon := by
  classical
  have hl (q : K) := exists_hillHminus_disc_trace_approximation q.val r hr hrpi epsilon hepsilon
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

/-- One H^-1 neighborhood controls all high discs along every straight source segment. -/
theorem exists_hillHminus_source_disc_trace_approximation
    (q : PeriodOneHminusOne) (r : ℝ) (hr : 0 < r) (hrpi : r ≤ Real.pi/4)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ N : ℕ, ∃ V : Set PeriodOneHminusOne, 0 < N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ a ∈ V, ∀ s ∈ Icc (0 : ℝ) 1, ∀ n : ℕ, N ≤ n →
        ∀ z ∈ closedBall ((Real.pi : ℂ)*n) r,
          ‖hillHminusDiscriminant ((s : ℂ) • a) (z^2)-2*cos z‖ ≤ epsilon := by
  let K : Set PeriodOneHminusOne := (fun s : ℝ => (s : ℂ) • q) '' Icc (0 : ℝ) 1
  have hK : IsCompact K := isCompact_Icc.image (by fun_prop)
  obtain ⟨N,U,hN,hU,hKU,hd⟩ :=
    exists_hillHminus_disc_trace_approximation_near_compact K hK r hr hrpi epsilon hepsilon
  let D : Set (ℂ × PeriodOneHminusOne) := univ ×ˢ U
  let V : Set PeriodOneHminusOne := (fun a => ((0 : ℂ),a)) ⁻¹' sourceSegmentDomain 0 D
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
