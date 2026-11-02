import NLS.KdV.ClassicalSpectralEmbedding
import NLS.KdV.ClassicalSourcePrimitive
import NLS.ZakharovShabat.PeriodicCounting

/-! # Uniform spectral contour avoidance for the actual Hill primitive

Pull the existing complex periodic counting neighborhoods back through
the actual physical Fourier realization of (-1,-q). Compactness of the
straight potential segment gives one cutoff and one open potential
neighborhood. The quadratic images of all high frequency circles then
lie in the constructed free-normalized primitive's continuation domain.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ZakharovShabat NLS.ComplexAnalysis
namespace NLS.KdV

/-- One common cutoff and open neighborhood support the actual complex
periodic counting data near every potential in a compact set. -/
theorem exists_classicalHillCounting_near_compact
    (K : Set (NLS.LinearVolterra.Curve ℂ)) (hK : IsCompact K) :
    ∃ N : ℕ, ∃ V : Set (NLS.LinearVolterra.Curve ℂ), 0 < N ∧ IsOpen V ∧ K ⊆ V ∧
      ∀ q ∈ V, ∀ M : ℕ, N ≤ M →
        PeriodicCountingData (by simp) (classicalHillCoefficientPotential q) M := by
  classical
  have hl (q : K) : ∃ N : ℕ, ∃ V : Set (NLS.LinearVolterra.Curve ℂ),
      0 < N ∧ IsOpen V ∧ q.val ∈ V ∧ ∀ a ∈ V, ∀ M : ℕ, N ≤ M →
        PeriodicCountingData (by simp) (classicalHillCoefficientPotential a) M := by
    obtain ⟨N,U,hN,hU,_,hq,_,_,_,hd⟩ :=
      exists_uniform_periodicCountingData (by simp) (classicalHillCoefficientPotential q.val)
    exact ⟨N,classicalHillCoefficientPotential ⁻¹' U,hN,
      hU.preimage continuous_classicalHillCoefficientPotential,hq,fun a ha M hM => hd _ ha M hM⟩
  choose N V hN hV hqV hd using hl
  obtain ⟨S,hS⟩ := hK.elim_finite_subcover V hV
    (fun q hq => mem_iUnion.mpr ⟨⟨q,hq⟩,hqV ⟨q,hq⟩⟩)
  refine ⟨1+∑ q ∈ S, N q,⋃ q ∈ S, V q,by omega,
    isOpen_iUnion (fun q => isOpen_iUnion (fun _ => hV q)),hS,?_⟩
  intro q hq M hM
  obtain ⟨a,ha⟩ := mem_iUnion.mp hq
  obtain ⟨haS,hqa⟩ := mem_iUnion.mp ha
  have hNa : N a ≤ ∑ b ∈ S, N b := Finset.single_le_sum (fun _ _ => Nat.zero_le _) haS
  exact hd a q hqa M (by omega)

/-- High frequency discs lie strictly in the right half-plane. -/
theorem re_pos_of_high_closedBall (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ closedBall ((Real.pi : ℂ)*n) (Real.pi/4)) : 0 < z.re := by
  have hnorm : ‖z-(Real.pi : ℂ)*n‖ ≤ Real.pi/4 := by
    simpa only [mem_closedBall,dist_eq_norm] using hz
  have hre : |z.re-Real.pi*n| ≤ Real.pi/4 := by
    simpa only [sub_re,mul_re,ofReal_re,ofReal_im,natCast_re,natCast_im,
      mul_zero,zero_mul,sub_zero] using
      (abs_re_le_norm (z-(Real.pi : ℂ)*n)).trans hnorm
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith [Real.pi_pos,(abs_le.mp hre).1]

/-- The squared closed high-frequency disc lies in the energy slit plane. -/
theorem sq_mem_slitPlane_of_high_closedBall (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ closedBall ((Real.pi : ℂ)*n) (Real.pi/4)) : z^2 ∈ slitPlane := by
  have hzre := re_pos_of_high_closedBall n hn z hz
  rw [mem_slitPlane_iff]
  by_cases hi : z.im = 0
  · left
    simp only [pow_two,mul_re,hi,mul_zero,sub_zero]
    positivity
  · right
    simp only [pow_two,mul_im]
    have hprod : z.re*z.im ≠ 0 := mul_ne_zero hzre.ne' hi
    intro he
    apply hprod
    linear_combination he/2

/-- Squaring is injective on each of the positive high-frequency discs. -/
theorem sq_injOn_high_closedBall (n : ℕ) (hn : 1 ≤ n) :
    InjOn (fun z : ℂ => z^2) (closedBall ((Real.pi : ℂ)*n) (Real.pi/4)) := by
  intro z hz w hw he
  rcases eq_or_eq_neg_of_sq_eq_sq z w he with h | h
  · exact h
  have hzre := re_pos_of_high_closedBall n hn z hz
  have hwre := re_pos_of_high_closedBall n hn w hw
  have he := congrArg Complex.re h
  simp only [neg_re] at he
  linarith

/-- Every squared high-frequency circle lies in the energy slit plane. -/
theorem sq_mem_slitPlane_of_high_circle (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ sphere ((Real.pi : ℂ)*n) (Real.pi/4)) : z^2 ∈ slitPlane :=
  sq_mem_slitPlane_of_high_closedBall n hn z (sphere_subset_closedBall hz)

/-- For each continuous potential there is one cutoff and one complex
open neighborhood on which the entire high-contour family avoids every
actual branch point along the straight source paths from zero. -/
theorem exists_classicalHill_high_contour_neighborhood (q : NLS.LinearVolterra.Curve ℂ) :
    ∃ N : ℕ, ∃ V : Set (NLS.LinearVolterra.Curve ℂ),
      0 < N ∧ IsOpen V ∧ q ∈ V ∧
        ∀ a ∈ V, ∀ n : ℕ, N < n → ∀ z ∈ sphere ((Real.pi : ℂ)*n) (Real.pi/4),
          (z^2,a) ∈ classicalHillContinuationDomain := by
  let K : Set (NLS.LinearVolterra.Curve ℂ) :=
    (fun s : ℝ => (s : ℂ) • q) '' Icc (0 : ℝ) 1
  have hK : IsCompact K := isCompact_Icc.image (by fun_prop)
  obtain ⟨N,U,hN,hU,hKU,hdata⟩ := exists_classicalHillCounting_near_compact K hK
  let D : Set (ℂ × NLS.LinearVolterra.Curve ℂ) := univ ×ˢ U
  let V : Set (NLS.LinearVolterra.Curve ℂ) :=
    (fun a => ((0 : ℂ),a)) ⁻¹' sourceSegmentDomain 0 D
  have hV : IsOpen V := (isOpen_sourceSegmentDomain 0 D (isOpen_univ.prod hU)).preimage
    (continuous_const.prodMk continuous_id)
  have hqV : q ∈ V := by
    intro s hs
    exact ⟨mem_univ _,by simpa only [sourceSegmentMap,zero_add,sub_zero] using hKU ⟨s,hs,rfl⟩⟩
  refine ⟨N,V,hN,hV,hqV,?_⟩
  intro a ha n hn z hz s hs
  have haU : (s : ℂ) • a ∈ U := by
    simpa only [sourceSegmentMap,zero_add,sub_zero] using (ha s hs).2
  have hc := (hdata _ haU N le_rfl).disk_resolvent (n : ℤ) (by simpa using hn)
  have hneq : classicalHillRadicand (z^2,(s : ℂ) • a) ≠ 0 := by
    intro he
    have hspec := (classicalHillRadicand_sq_eq_zero_iff_periodicSpectrum ((s : ℂ) • a) z).mp he
    have hz' : z ∈ sphere ((Real.pi : ℂ)*(n : ℤ)) (Real.pi/4) := by
      simpa only [Int.cast_natCast] using hz
    have hres := hc hz'
    exact hspec hres
  have hn1 : 1 ≤ n := Nat.succ_le_of_lt ((Nat.zero_le N).trans_lt hn)
  simp only [sourceSegmentMap,zero_add,sub_zero]
  exact ⟨sq_mem_slitPlane_of_high_circle n hn1 z hz,hneq⟩

end NLS.KdV
