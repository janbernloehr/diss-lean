import NLS.ZakharovShabat.SourceFullAbelianInverseMassContour
import NLS.ComplexAnalysis.ShiftedSquareWeightedCircle
import NLS.ZakharovShabat.SourcePrimitivePowerCircle

/-! Exact local reduction of the inverse-frequency squared full primitive
contour to the SAME indexed primitive with weight 1/z. The selected
square is filled analytically; zero is explicitly outside its whole disc. -/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily
open NLS.ComplexAnalysis
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}

theorem inverse_square_circle_eq_inverse_primitive
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (n : ℤ)
    (ψ : CoeffPair p) (hψ : ψ ∈ ball C.discs.source.val C.discs.sourceRadius)
    (R : ℝ) (hi : C.discs.inner n ≤ R) (ho : R < C.discs.outer n)
    (hz : (0:ℂ) ∉ closedBall (C.discs.center n) R) :
    (∮ z in C(C.discs.center n,R), (sourceFullAbelianPrimitive hp hp1 W 0 (z,ψ))^2/z)=
      (-2*I*(Real.pi:ℂ)*n)*(∮ z in C(C.discs.center n,R),
        sourceFullAbelianPrimitive hp hp1 W n (z,ψ)/z) := by
  obtain ⟨D⟩ := C.charts ψ hψ
  have hR : 0 ≤ R := (C.discs.inner_pos n).le.trans hi
  have hroot : sphere (C.discs.center n) R ⊆ sourceCanonicalRootDomain hp hp1 ψ :=
    C.intermediate_circle_root n ψ hψ R hi ho
  let f : ℂ → ℂ := fun z => sourceFullAbelianPrimitive hp hp1 W n (z,ψ)
  have hf : ContinuousOn f (sphere (C.discs.center n) R) :=
    (sourceFullAbelianPrimitive_spectral_analytic D n).continuousOn.mono
      (hroot.trans (sourceCanonicalRootDomain_subset_openGapComplement hp hp1 ψ))
  have hq : AnalyticOnNhd ℂ (fun z : ℂ => z⁻¹) (closedBall (C.discs.center n) R) := by
    intro z hzc
    exact analyticAt_id.inv (fun he => hz (he ▸ hzc))
  have hQ : AnalyticOnNhd ℂ (fun z => C.square n (z,ψ)) (closedBall (C.discs.center n) R) :=
    (C.square_analytic n ψ hψ).mono (closedBall_subset_ball ho)
  have he : EqOn (fun z => f z^2) (fun z => C.square n (z,ψ)) (sphere (C.discs.center n) R) := by
    intro z hzc
    exact (C.square_eq_fullPrimitive_sq n ψ hψ z
      ⟨closedBall_subset_ball ho (sphere_subset_closedBall hzc),hroot hzc n⟩).symm
  have hc := circleIntegral_shifted_square_weight f (fun z => C.square n (z,ψ))
    (fun z : ℂ => z⁻¹) (-I*(Real.pi:ℂ)*n) (C.discs.center n) R hR hf hQ hq he
  have hL : (∮ z in C(C.discs.center n,R), (sourceFullAbelianPrimitive hp hp1 W 0 (z,ψ))^2/z)=
      ∮ z in C(C.discs.center n,R), z⁻¹*(f z+(-I*(Real.pi:ℂ)*n))^2 := by
    apply circleIntegral.integral_congr hR
    intro z hzc
    dsimp only [f]
    rw [sourceFullAbelianPrimitive_index_shift D n z
      (sourceCanonicalRootDomain_subset_openGapComplement hp hp1 ψ (hroot hzc))]
    ring
  have hlin : (∮ z in C(C.discs.center n,R), z⁻¹*f z)=
      ∮ z in C(C.discs.center n,R), sourceFullAbelianPrimitive hp hp1 W n (z,ψ)/z := by
    apply circleIntegral.integral_congr hR
    intro z _
    dsimp only [f]
    ring
  rw [hL,hc,hlin]
  ring

end NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily
