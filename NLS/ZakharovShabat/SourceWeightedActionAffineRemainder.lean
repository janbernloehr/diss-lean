import NLS.ZakharovShabat.SourceNormalizedWeightedAction
import NLS.ZakharovShabat.SourceFullAbelianGapComparison

/-! The first weighted normalized action is its midpoint times the
zeroth normalized action plus a regular primitive-boundary integral.
Its estimate retains one gap factor even at collapse. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex MeasureTheory NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily
variable {p : ℝ≥0∞} [Fact (1≤p)] {hp : p≠⊤} {hp1 : 1<p} {W : Set (CoeffPair p)}

theorem normalizedWeightedAction_one_affine_remainder
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (ψ : CoeffPair p)
    (hψ : ψ∈ball C.discs.source.val C.discs.sourceRadius) (n : ℤ) :
    C.normalizedWeightedAction n 1 ψ=
      sourceStandardRootMidpoint hp hp1 ψ n*C.normalizedWeightedAction n 0 ψ+
        (1/(2*Real.pi) : ℂ)*∫ θ in (0 : ℝ)..Real.pi,
          (Real.sin θ : ℂ)*(Real.cos θ : ℂ)*C.gapBoundary n ψ θ true := by
  let τ := sourceStandardRootMidpoint hp hp1 ψ n
  let δ := sourceStandardRootHalfGap hp hp1 ψ n
  let Q := fun z => sourceFullAbelianCauchyQuotient hp hp1 W n (C.discs.center n) (C.discs.outer n) (z,ψ)
  let z := fun θ : ℝ => τ+δ*(Real.cos θ : ℂ)
  have hz : Continuous z := by dsimp only [z]; fun_prop
  have hQ : Continuous (fun θ => Q (z θ)) := by
    apply continuous_iff_continuousAt.mpr
    intro θ
    have hmem := C.segment_subset_outer n ψ hψ
      (sourceCanonicalRootGapPoint_mem_segment hp hp1 ψ n (Real.cos θ)
        (Real.neg_one_le_cos θ) (Real.cos_le_one θ))
    exact (C.quotient_slice_analytic n ψ hψ (z θ) hmem).continuousAt.comp hz.continuousAt
  let g0 := fun θ : ℝ => (Real.sin θ : ℂ)^2*Q (z θ)
  let gB := fun θ : ℝ => (Real.sin θ : ℂ)*(Real.cos θ : ℂ)*C.gapBoundary n ψ θ true
  have hsin : Continuous (fun θ : ℝ => (Real.sin θ : ℂ)) := Complex.continuous_ofReal.comp Real.continuous_sin
  have hcos : Continuous (fun θ : ℝ => (Real.cos θ : ℂ)) := Complex.continuous_ofReal.comp Real.continuous_cos
  have h0 : Continuous g0 := (hsin.pow 2).mul hQ
  have hgb : Continuous (fun θ : ℝ => C.gapBoundary n ψ θ true) := by
    change Continuous (fun θ : ℝ => -I*(δ*(Real.sin θ : ℂ)*Q (z θ)))
    exact ((hsin.const_mul δ).mul hQ).const_mul (-I)
  have hB : Continuous gB := (hsin.mul hcos).mul hgb
  have he (θ : ℝ) : (Real.sin θ : ℂ)^2*((z θ)^1*Q (z θ))=τ*g0 θ+I*gB θ := by
    change (Real.sin θ : ℂ)^2*((τ+δ*(Real.cos θ : ℂ))^1*Q (z θ))=
      τ*((Real.sin θ : ℂ)^2*Q (z θ))+
        I*((Real.sin θ : ℂ)*(Real.cos θ : ℂ)*(-I*(δ*(Real.sin θ : ℂ)*Q (z θ))))
    simp only [pow_one]
    linear_combination (δ*(Real.sin θ : ℂ)^2*(Real.cos θ : ℂ)*Q (z θ))*I_sq
  have hi : (∫ θ in (0 : ℝ)..Real.pi, (Real.sin θ : ℂ)^2*((z θ)^1*Q (z θ)))=
      τ*(∫ θ in (0 : ℝ)..Real.pi, g0 θ)+I*(∫ θ in (0 : ℝ)..Real.pi, gB θ) := by
    simp_rw [he]
    rw [intervalIntegral.integral_add ((h0.const_mul τ).intervalIntegrable _ _)
      ((hB.const_mul I).intervalIntegrable _ _),intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  change (-I/(2*Real.pi : ℂ))*(∫ θ in (0 : ℝ)..Real.pi, (Real.sin θ : ℂ)^2*((z θ)^1*Q (z θ)))=
    τ*((-I/(2*Real.pi : ℂ))*(∫ θ in (0 : ℝ)..Real.pi, (Real.sin θ : ℂ)^2*((z θ)^0*Q (z θ))))+
      (1/(2*Real.pi) : ℂ)*(∫ θ in (0 : ℝ)..Real.pi, gB θ)
  simp only [pow_zero,one_mul]
  rw [hi]
  change _=τ*((-I/(2*Real.pi : ℂ))*(∫ θ in (0 : ℝ)..Real.pi, g0 θ))+_
  have hpi : (Real.pi : ℂ)≠0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  linear_combination -(∫ θ in (0 : ℝ)..Real.pi, gB θ)*I_sq

theorem norm_normalizedWeightedAction_one_affine_remainder_le
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (ψ : CoeffPair p)
    (hψ : ψ∈ball C.discs.source.val C.discs.sourceRadius) (n : ℤ) (B : ℝ)
    (hb : ∀ θ∈Icc (0 : ℝ) Real.pi, ‖C.gapBoundary n ψ θ true‖≤B) :
    ‖C.normalizedWeightedAction n 1 ψ-
      sourceStandardRootMidpoint hp hp1 ψ n*C.normalizedWeightedAction n 0 ψ‖≤B/2 := by
  have hi : ‖∫ θ in (0 : ℝ)..Real.pi,
      (Real.sin θ : ℂ)*(Real.cos θ : ℂ)*C.gapBoundary n ψ θ true‖≤B*Real.pi := by
    apply (intervalIntegral.norm_integral_le_of_norm_le_const ?_).trans_eq
      (by rw [sub_zero,abs_of_pos Real.pi_pos])
    intro θ hθ
    have hθ' : θ∈Icc (0 : ℝ) Real.pi := by
      simpa only [uIcc_of_le Real.pi_pos.le] using uIoc_subset_uIcc hθ
    have hs : ‖(Real.sin θ : ℂ)‖≤1 := by simpa only [Complex.norm_real,Real.norm_eq_abs] using Real.abs_sin_le_one θ
    have hc : ‖(Real.cos θ : ℂ)‖≤1 := by simpa only [Complex.norm_real,Real.norm_eq_abs] using Real.abs_cos_le_one θ
    rw [norm_mul,norm_mul]
    calc
      _≤1*‖C.gapBoundary n ψ θ true‖ := mul_le_mul_of_nonneg_right
        (by nlinarith [norm_nonneg (Real.sin θ : ℂ),norm_nonneg (Real.cos θ : ℂ)]) (norm_nonneg _)
      _≤B := by simpa only [one_mul] using hb θ hθ'
  rw [C.normalizedWeightedAction_one_affine_remainder ψ hψ n,add_sub_cancel_left,norm_mul]
  have hcoef : ‖(1/(2*Real.pi) : ℂ)‖=1/(2*Real.pi) := by
    simp only [norm_div,norm_one,norm_mul,norm_ofNat,Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le]
  rw [hcoef]
  apply (mul_le_mul_of_nonneg_left hi (by positivity : 0≤1/(2*Real.pi))).trans_eq
  field_simp

end NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily
