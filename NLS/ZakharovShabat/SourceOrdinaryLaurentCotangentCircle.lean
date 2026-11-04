import NLS.ZakharovShabat.SourceDiagonalLaurentDerivative
import NLS.ZakharovShabat.SourceDiagonalLaurentOrdinaryDifferential
import NLS.ZakharovShabat.SourceActionPoissonGradient

/-! # The ordinary source action cotangent on the zero-excluding Laurent circle -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem fderiv_sourceComplexAction_eq_Laurent_cotangent_circle
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realDiagonalSourceLocus p) (n : ℤ) (hn : n ≠ 0) :
    let C := (sourceDiagonalLaurentAtlas hp hp1).localChart φ
    fderiv ℂ (sourceComplexAction hp hp1 n) φ.val =
      -(Real.pi : ℂ)⁻¹ • ∮ z in C(C.cauchy.discs.center n,C.contourRadius n),
        sourceActionVariationCotangent hp hp1 φ.val z := by
  let A := sourceDiagonalLaurentAtlas hp hp1
  let C := A.localChart φ
  have hφ : φ.val ∈ ball φ.val C.radius := mem_ball_self C.radius_pos
  have hlocal : sourceDiagonalLaurentAction hp hp1 n 1 =ᶠ[𝓝 φ.val] C.action n 1 := by
    filter_upwards [isOpen_ball.mem_nhds hφ] with ψ hψ
    exact A.action_eq_local n 1 hn φ hψ
  have hI : fderiv ℂ (sourceComplexAction hp hp1 n) φ.val = fderiv ℂ (C.action n 1) φ.val :=
    (fderiv_sourceDiagonalLaurentAction_one hp hp1 φ n hn).symm.trans hlocal.fderiv_eq
  have hcircle : sphere (C.cauchy.discs.center n) (C.contourRadius n) ⊆ sourceCanonicalRootDomain hp hp1 φ.val := by
    intro z hz
    exact C.cauchy.intermediate_circle_root n φ.val (C.source_subset hφ) _
      (C.contourRadius_bounds n).1 (C.contourRadius_bounds n).2 z hz
  have hint := circleIntegrable_sourceActionVariationCotangent hp hp1 φ.val _ _ (C.contourRadius_pos n).le hcircle
  change fderiv ℂ (sourceComplexAction hp hp1 n) φ.val = _
  rw [hI]
  apply ContinuousLinearMap.ext
  intro h
  have heval := map_circleIntegral (ContinuousLinearMap.apply ℂ ℂ h) hint
  change (∮ z in C(C.cauchy.discs.center n,C.contourRadius n), sourceActionVariationCotangent hp hp1 φ.val z) h =
    ∮ z in C(C.cauchy.discs.center n,C.contourRadius n), (sourceActionVariationCotangent hp hp1 φ.val z) h at heval
  rw [C.fderiv_action ⟨φ.val,φ.property.1⟩ hφ n 1 hn h]
  simp only [sub_self,zpow_zero,one_mul,smul_apply,smul_eq_mul]
  rw [heval]
  congr 1
  apply circleIntegral.integral_congr (C.contourRadius_pos n).le
  intro z _
  simp only [sourceActionVariationCotangent,smul_apply,smul_eq_mul,div_eq_inv_mul]

end NLS.ZakharovShabat
