import NLS.ZakharovShabat.SourceFullAbelianMassContour
import NLS.ZakharovShabat.SourceWeightedPrimitiveBoundary
import NLS.ComplexAnalysis.FiniteCircleHoleDecomposition

/-! # Mass decomposed over noncentral gaps at a collapsed zero gap

The literal squared primitive divided by frequency is analytic at zero.
Finite-hole Cauchy deformation therefore has no extra zero-frequency
residue. Each noncentral contribution is the original selected primitive
weighted by inverse frequency, with its exact index constant.
-/
noncomputable section
open Set Metric Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
variable (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)

theorem fullPrimitive_zero_of_central_endpoints (ψ : CoeffPair p)
    (hψ : ψ ∈ ball C.discs.source.val C.discs.sourceRadius)
    (hl : canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) 0 = 0)
    (hr : canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) 0 = 0) :
    sourceFullAbelianPrimitive hp hp1 W 0 (0,ψ) = 0 := by
  have hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) 0 = 0 := by
    rw [canonicalPeriodicGap,hl,hr,sub_self]
  simpa only [sub_self,mul_zero] using C.fullPrimitive_collapsed_endpoint_value
    0 0 ψ hψ hgap 0 (Set.mem_insert_iff.mpr (Or.inl hl.symm))

theorem square_over_frequency_analytic_of_central_endpoints (φ : realTypeSourceSubmodule p)
    (hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius)
    (hl : canonicalPeriodicLeft hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) 0 = 0)
    (hr : canonicalPeriodicRight hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) 0 = 0) :
    AnalyticOnNhd ℂ (fun z => (sourceFullAbelianPrimitive hp hp1 W 0 (z,φ.val))^2/z)
      (sourceOpenGapComplement hp hp1 φ.val) := by
  obtain ⟨E⟩ := C.charts φ.val hφ
  have hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) 0 = 0 := by
    rw [canonicalPeriodicGap,hl,hr,sub_self]
  have hend : (0 : ℂ) ∈ ({canonicalPeriodicLeft hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) 0,
      canonicalPeriodicRight hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) 0} : Set ℂ) := Set.mem_insert_iff.mpr (Or.inl hl.symm)
  exact analyticOnNhd_square_div_id_of_zero _ _
    (isOpen_sourceOpenGapComplement_of_realType hp hp1 φ.val φ.property)
    (C.ball_subset_openGapComplement_of_collapsed 0 φ.val hφ hgap (C.endpoint_mem_ball 0 φ.val hφ 0 hend))
    (sourceFullAbelianPrimitive_spectral_analytic E 0) (C.fullPrimitive_zero_of_central_endpoints φ.val hφ hl hr)

/-- The selected square and constant term have zero contour. Only the
actual signed index offset times the inverse-frequency primitive remains. -/
theorem square_over_frequency_circle (ψ : CoeffPair p)
    (hψ : ψ ∈ ball C.discs.source.val C.discs.sourceRadius) (n : ℤ)
    (R : ℝ) (hinner : C.discs.inner n ≤ R) (houter : R < C.discs.outer n)
    (hzero : (0 : ℂ) ∉ ball (C.discs.center n) (C.discs.outer n)) :
    (∮ z in C(C.discs.center n,R), (sourceFullAbelianPrimitive hp hp1 W 0 (z,ψ))^2/z) =
      (-2*I*(Real.pi : ℂ)*n)*(∮ z in C(C.discs.center n,R), sourceFullAbelianPrimitive hp hp1 W n (z,ψ)/z) := by
  let H : ℂ → ℂ := fun z => (C.square n (z,ψ)+(I*(Real.pi : ℂ)*n)^2)/z
  have hR : 0 < R := (C.discs.inner_pos n).trans_le hinner
  have hz0 (z : ℂ) (hz : z ∈ closedBall (C.discs.center n) R) : z ≠ 0 := by
    rintro rfl
    exact hzero (closedBall_subset_ball houter hz)
  have hH : AnalyticOnNhd ℂ H (closedBall (C.discs.center n) R) := by
    intro z hz
    exact ((C.square_analytic n ψ hψ z (closedBall_subset_ball houter hz)).add analyticAt_const).div
      analyticAt_id (hz0 z hz)
  have hH0 : (∮ z in C(C.discs.center n,R), H z) = 0 :=
    (DiffContOnCl.mk_ball (hH.differentiableOn.mono ball_subset_closedBall) hH.continuousOn).circleIntegral_eq_zero hR.le
  obtain ⟨E⟩ := C.charts ψ hψ
  have hfi : CircleIntegrable (fun z => sourceFullAbelianPrimitive hp hp1 W n (z,ψ)/z) (C.discs.center n) R := by
    apply ContinuousOn.circleIntegrable hR.le
    intro z hz
    exact ((sourceFullAbelianPrimitive_hasDerivAt E n z
      (C.intermediate_circle_root n ψ hψ R hinner houter z hz)).continuousAt.div
        continuousAt_id (hz0 z (sphere_subset_closedBall hz))).continuousWithinAt
  have hci : CircleIntegrable (fun z => (-2*I*(Real.pi : ℂ)*n)*
      (sourceFullAbelianPrimitive hp hp1 W n (z,ψ)/z)) (C.discs.center n) R := by
    have hs := hfi.const_smul (a := (-2*I*(Real.pi : ℂ)*n))
    change CircleIntegrable (fun z => (-2*I*(Real.pi : ℂ)*n) •
      (sourceFullAbelianPrimitive hp hp1 W n (z,ψ)/z)) (C.discs.center n) R at hs
    simpa only [smul_eq_mul] using hs
  calc
    _ = ∮ z in C(C.discs.center n,R), H z+(-2*I*(Real.pi : ℂ)*n)*
        (sourceFullAbelianPrimitive hp hp1 W n (z,ψ)/z) := by
      apply circleIntegral.integral_congr hR.le
      intro z hz
      have hzn : z ∈ ball (C.discs.center n) (C.discs.outer n) \ sourcePeriodicSegment hp hp1 ψ n :=
        ⟨closedBall_subset_ball houter (sphere_subset_closedBall hz),
          C.intermediate_circle_root n ψ hψ R hinner houter z hz n⟩
      dsimp only [H]
      rw [C.square_eq_fullPrimitive_sq n ψ hψ z hzn,
        C.fullPrimitive_eq_cauchy n 0 ψ hψ z hzn,C.fullPrimitive_eq_cauchy n n ψ hψ z hzn]
      simp only [Int.cast_zero,zero_sub,sub_self,mul_zero,add_zero]
      ring
    _ = _ := by
      rw [circleIntegral.integral_add (hH.continuousOn.mono sphere_subset_closedBall |>.circleIntegrable hR.le)
        hci,hH0,zero_add,circleIntegral.integral_const_mul]

end NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily
