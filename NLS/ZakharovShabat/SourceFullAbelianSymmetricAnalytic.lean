import NLS.ZakharovShabat.SourceHigherActionComplexCosine

/-! # Symmetric spectral coordinates on full Cauchy source balls

Two fixed exterior root values recover the midpoint and squared gap
analytically throughout the original ball, including collapsed gaps.
-/
noncomputable section
open Set Metric Complex NLS NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}

/-- The midpoint and squared gap are analytic on the entire common source ball. -/
theorem symmetric_analytic (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (n : ℤ) :
    AnalyticOnNhd ℂ (fun ψ => sourceStandardRootMidpoint hp hp1 ψ n)
      (ball C.discs.source.val C.discs.sourceRadius) ∧
    AnalyticOnNhd ℂ (fun ψ => (canonicalPeriodicGap hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) n)^2)
      (ball C.discs.source.val C.discs.sourceRadius) := by
  let R := C.discs.outer n
  have hR : 0 < R := (C.discs.inner_pos n).trans (C.discs.inner_lt n)
  let z₁ := C.discs.center n + (R:ℂ)
  let z₂ := C.discs.center n - (R:ℂ)
  have hz₁ : z₁ ∈ sphere (C.discs.center n) R := by
    simp [z₁,abs_of_pos hR]
  have hz₂ : z₂ ∈ sphere (C.discs.center n) R := by
    simp [z₂,abs_of_pos hR]
  have hz : z₁-z₂ ≠ 0 := by
    have he : z₁-z₂ = 2*(R:ℂ) := by dsimp [z₁,z₂]; ring
    rw [he]
    exact mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr hR.ne')
  let f₁ := fun ψ => (sourceStandardRoot hp hp1 ψ n z₁)^2
  let f₂ := fun ψ => (sourceStandardRoot hp hp1 ψ n z₂)^2
  have ha₁ : AnalyticOnNhd ℂ f₁ (ball C.discs.source.val C.discs.sourceRadius) := by
    intro ψ hψ
    exact ((C.root_analytic n (z₁,ψ) ⟨hψ,C.circle_root n ψ hψ z₁ hz₁ n⟩).comp
      (f := fun χ : CoeffPair p => (z₁,χ)) (analyticAt_const.prod analyticAt_id)).pow 2
  have ha₂ : AnalyticOnNhd ℂ f₂ (ball C.discs.source.val C.discs.sourceRadius) := by
    intro ψ hψ
    exact ((C.root_analytic n (z₂,ψ) ⟨hψ,C.circle_root n ψ hψ z₂ hz₂ n⟩).comp
      (f := fun χ : CoeffPair p => (z₂,χ)) (analyticAt_const.prod analyticAt_id)).pow 2
  have hm : ∀ ψ ∈ ball C.discs.source.val C.discs.sourceRadius,
      sourceStandardRootMidpoint hp hp1 ψ n = (z₁^2-z₂^2-(f₁ ψ-f₂ ψ))/(2*(z₁-z₂)) := by
    intro ψ hψ
    dsimp [f₁,f₂]
    rw [sourceStandardRoot_sq_of_not_mem_segment hp hp1 ψ n z₁ (C.circle_root n ψ hψ z₁ hz₁ n),
      sourceStandardRoot_sq_of_not_mem_segment hp hp1 ψ n z₂ (C.circle_root n ψ hψ z₂ hz₂ n)]
    unfold sourceStandardRootMidpoint canonicalPeriodicMidpoint
    field_simp [hz]
    ring
  have ham : AnalyticOnNhd ℂ (fun ψ => sourceStandardRootMidpoint hp hp1 ψ n)
      (ball C.discs.source.val C.discs.sourceRadius) := by
    intro ψ hψ
    have ha : AnalyticAt ℂ (fun χ => (z₁^2-z₂^2-(f₁ χ-f₂ χ))/(2*(z₁-z₂))) ψ :=
      (analyticAt_const.sub ((ha₁ ψ hψ).sub (ha₂ ψ hψ))).div_const
    apply ha.congr
    filter_upwards [isOpen_ball.mem_nhds hψ] with χ hχ
    exact (hm χ hχ).symm
  refine ⟨ham,?_⟩
  intro ψ hψ
  have ha : AnalyticAt ℂ (fun χ => 4*((sourceStandardRootMidpoint hp hp1 χ n-z₁)^2-f₁ χ)) ψ :=
    analyticAt_const.mul (((ham ψ hψ).sub analyticAt_const).pow 2 |>.sub (ha₁ ψ hψ))
  apply ha.congr
  filter_upwards [isOpen_ball.mem_nhds hψ] with χ hχ
  dsimp [f₁]
  rw [sourceStandardRoot_sq_of_not_mem_segment hp hp1 χ n z₁ (C.circle_root n χ hχ z₁ hz₁ n)]
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential χ) (periodOnePotential_mem χ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential χ) (periodOnePotential_mem χ) n
  change 4*(((l+r)/2-z₁)^2-(l-z₁)*(r-z₁)) = (r-l)^2
  ring
end NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily
