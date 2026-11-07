import NLS.ZakharovShabat.SourceNormalizedWeightedAction
import NLS.ZakharovShabat.SourceFullAbelianGapComparison
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! The raw zeroth action error follows from the actual primitive
boundary error, with two literal gap factors also at collapsed gaps. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex MeasureTheory
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily
variable {p : ℝ≥0∞} [Fact (1≤p)] {hp : p≠⊤} {hp1 : 1<p} {W : Set (CoeffPair p)}

theorem norm_raw_normalizedWeightedAction_zero_error_le
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (ψ : CoeffPair p)
    (hψ : ψ∈ball C.discs.source.val C.discs.sourceRadius) (n : ℤ)
    (E : ℝ)
    (hb : ∀ θ∈Icc (0 : ℝ) Real.pi,
      ‖C.gapBoundary n ψ θ true-I*sourceStandardRootGapBoundary hp hp1 ψ n θ true‖≤
        ‖canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n‖*E) :
    ‖(canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)^2*
      C.normalizedWeightedAction n 0 ψ-
        (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)^2/4‖≤
          ‖canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n‖^2*E := by
  let γ := canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  let δ := sourceStandardRootHalfGap hp hp1 ψ n
  let τ := sourceStandardRootMidpoint hp hp1 ψ n
  let Q := fun z => sourceFullAbelianCauchyQuotient hp hp1 W n
    (C.discs.center n) (C.discs.outer n) (z,ψ)
  have hz : Continuous (fun θ : ℝ => τ+δ*(Real.cos θ : ℂ)) := by fun_prop
  have hQ : Continuous (fun θ : ℝ => Q (τ+δ*(Real.cos θ : ℂ))) := by
    apply continuous_iff_continuousAt.mpr
    intro θ
    have hm := C.segment_subset_outer n ψ hψ
      (sourceCanonicalRootGapPoint_mem_segment hp hp1 ψ n (Real.cos θ)
        (Real.neg_one_le_cos θ) (Real.cos_le_one θ))
    exact (C.quotient_slice_analytic n ψ hψ (τ+δ*(Real.cos θ : ℂ)) hm).continuousAt.comp
      (f := fun θ : ℝ => τ+δ*(Real.cos θ : ℂ)) hz.continuousAt
  have hsin : Continuous (fun θ : ℝ => (Real.sin θ : ℂ)) := continuous_ofReal.comp Real.continuous_sin
  have hboundary : Continuous (fun θ : ℝ => C.gapBoundary n ψ θ true) := by
    change Continuous (fun θ : ℝ => -I*(δ*(Real.sin θ : ℂ)*Q (τ+δ*(Real.cos θ : ℂ))))
    exact ((hsin.const_mul δ).mul hQ).const_mul (-I)
  let f := fun θ : ℝ => (δ*(Real.sin θ : ℂ))*C.gapBoundary n ψ θ true
  let g := fun θ : ℝ => (δ*(Real.sin θ : ℂ))^2
  have hf : Continuous f := (hsin.const_mul δ).mul hboundary
  have hg : Continuous g := (hsin.const_mul δ).pow 2
  have hroot (θ : ℝ) : I*sourceStandardRootGapBoundary hp hp1 ψ n θ true=δ*(Real.sin θ : ℂ) := by
    simp only [sourceStandardRootGapBoundary,ite_true,mul_neg,← mul_assoc,I_mul_I,neg_neg,one_mul,δ]
  have hfree : (2/Real.pi : ℂ)*(∫ θ in (0 : ℝ)..Real.pi, g θ)=γ^2/4 := by
    have hi : (∫ θ in (0 : ℝ)..Real.pi, (Real.sin θ : ℂ)^2)=(Real.pi : ℂ)/2 := by
      simp only [← ofReal_pow,intervalIntegral.integral_ofReal,integral_sin_sq,
        Real.sin_zero,Real.sin_pi,zero_mul,sub_zero,zero_add,ofReal_div,ofReal_ofNat]
    dsimp only [g]
    simp_rw [mul_pow]
    rw [intervalIntegral.integral_const_mul,hi]
    dsimp only [δ,sourceStandardRootHalfGap,γ]
    have hpi : (Real.pi : ℂ)≠0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp
    ring
  have hraw := C.normalizedWeightedAction_boundary_factor n 0 ψ
  simp only [pow_zero,one_mul] at hraw
  have he : γ^2*C.normalizedWeightedAction n 0 ψ-γ^2/4=
      (2/Real.pi : ℂ)*(∫ θ in (0 : ℝ)..Real.pi,
        (δ*(Real.sin θ : ℂ))*(C.gapBoundary n ψ θ true-
          I*sourceStandardRootGapBoundary hp hp1 ψ n θ true)) := by
    rw [← hraw,← hfree,← mul_sub,← intervalIntegral.integral_sub
      (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _)]
    congr 1
    apply intervalIntegral.integral_congr
    intro θ _
    dsimp only [f,g]
    rw [hroot]
    ring
  have hi : ‖∫ θ in (0 : ℝ)..Real.pi, (δ*(Real.sin θ : ℂ))*
      (C.gapBoundary n ψ θ true-I*sourceStandardRootGapBoundary hp hp1 ψ n θ true)‖≤
        (‖γ‖^2*E/2)*Real.pi := by
    apply (intervalIntegral.norm_integral_le_of_norm_le_const ?_).trans_eq
      (by rw [sub_zero,abs_of_pos Real.pi_pos])
    intro θ hθ
    have hθ' : θ∈Icc (0 : ℝ) Real.pi := by
      simpa only [uIcc_of_le Real.pi_pos.le] using uIoc_subset_uIcc hθ
    have hs : ‖(Real.sin θ : ℂ)‖≤1 := by
      simpa only [Complex.norm_real,Real.norm_eq_abs] using Real.abs_sin_le_one θ
    have hδ : ‖δ‖=‖γ‖/2 := by simp only [δ,sourceStandardRootHalfGap,γ,norm_div,norm_ofNat]
    rw [norm_mul,norm_mul,hδ]
    calc
      _≤(‖γ‖/2*1)*(‖γ‖*E) := mul_le_mul
        (mul_le_mul_of_nonneg_left hs (by positivity)) (hb θ hθ') (norm_nonneg _) (by positivity)
      _=‖γ‖^2*E/2 := by ring
  change ‖γ^2*C.normalizedWeightedAction n 0 ψ-γ^2/4‖≤‖γ‖^2*E
  rw [he,norm_mul]
  have hcoef : ‖(2/Real.pi : ℂ)‖=2/Real.pi := by
    simp only [norm_div,norm_ofNat,Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le]
  rw [hcoef]
  apply (mul_le_mul_of_nonneg_left hi (by positivity : 0≤2/Real.pi)).trans_eq
  field_simp

end NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily
