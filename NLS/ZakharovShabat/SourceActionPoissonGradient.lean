import NLS.ZakharovShabat.SourceDiscriminantCotangent
import NLS.Poisson.SourceBracket
import NLS.ComplexAnalysis.BilinearCircleIntegral

/-! # Contour reduction of the actual action brackets

The existing directional contour derivative represents the entire
action cotangent as a Banach-valued circle integral. Continuous
bilinearity then expresses action brackets as iterated spectral
contour integrals. In particular, discriminant commutation on the
two isolating circles implies commutation of the indexed actions.
The discriminant commutation identity remains to be proved.
-/

noncomputable section
open Set Metric Complex NLS.ComplexAnalysis NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem fderiv_sourceComplexAction_eq_cotangent_circle_on_chart
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (ch : SourceRealActionBallChart hp hp1 n)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ))
    (hφ : φ ∈ ball ch.center ch.radius) :
    fderiv ℂ (sourceComplexAction hp hp1 n) φ =
      -(Real.pi : ℂ)⁻¹ •
        ∮ z in C(ch.spectralCenter,ch.spectralRadius), sourceActionVariationCotangent hp hp1 φ z := by
  have hgeom := ch.geometry φ hφ
  have hcircle : sphere ch.spectralCenter ch.spectralRadius ⊆ sourceCanonicalRootDomain hp hp1 φ :=
    sourceCanonicalRootDomain_of_enclosingCircle hp hp1 φ n
      ch.spectralCenter ch.spectralRadius hgeom.1 hgeom.2
  have hint := circleIntegrable_sourceActionVariationCotangent hp hp1 φ
    ch.spectralCenter ch.spectralRadius ch.spectralRadius_pos.le hcircle
  apply ContinuousLinearMap.ext
  intro h
  have heval := map_circleIntegral (ContinuousLinearMap.apply ℂ ℂ h) hint
  change (∮ z in C(ch.spectralCenter,ch.spectralRadius),
    sourceActionVariationCotangent hp hp1 φ z) h =
      ∮ z in C(ch.spectralCenter,ch.spectralRadius), (sourceActionVariationCotangent hp hp1 φ z) h at heval
  rw [fderiv_sourceComplexAction_eq_gradient_on_chart hp hp1 n ch φ hreal hφ h]
  simp only [smul_apply,smul_eq_mul]
  rw [heval]
  congr 1
  apply circleIntegral.integral_congr ch.spectralRadius_pos.le
  intro z _
  simp only [sourceActionVariationCotangent,sourceDiscriminantCotangent,smul_apply,
    smul_eq_mul,div_eq_mul_inv,mul_comm]

theorem sourceBivector_actionVariationCotangents_eq_discriminant_bracket
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2:ℝ≥0∞) ≤ p)
    (φ : CoeffPair p) (z w : ℂ) :
    sourceBivector h2p (sourceActionVariationCotangent hp hp1 φ z)
      (sourceActionVariationCotangent hp hp1 φ w) =
        (sourceCanonicalRoot hp hp1 φ z)⁻¹*(sourceCanonicalRoot hp hp1 φ w)⁻¹*
          sourceBracket h2p
            (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ) z)
            (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ) w) φ := by
  simp only [sourceActionVariationCotangent,sourceDiscriminantCotangent,sourceBracket,
    map_smul,smul_apply,smul_eq_mul]
  ring

theorem sourceBracket_actions_eq_double_circle
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2:ℝ≥0∞) ≤ p) (n m : ℤ)
    (cn : SourceRealActionBallChart hp hp1 n) (cm : SourceRealActionBallChart hp hp1 m)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ))
    (hn : φ ∈ ball cn.center cn.radius) (hm : φ ∈ ball cm.center cm.radius) :
    sourceBracket h2p (sourceComplexAction hp hp1 n) (sourceComplexAction hp hp1 m) φ =
      ((Real.pi : ℂ)⁻¹)^2*
        (∮ z in C(cn.spectralCenter,cn.spectralRadius),
          ∮ w in C(cm.spectralCenter,cm.spectralRadius),
            sourceBivector h2p (sourceActionVariationCotangent hp hp1 φ z)
              (sourceActionVariationCotangent hp hp1 φ w)) := by
  have hgn := cn.geometry φ hn
  have hgm := cm.geometry φ hm
  have hcn := sourceCanonicalRootDomain_of_enclosingCircle hp hp1 φ n
    cn.spectralCenter cn.spectralRadius hgn.1 hgn.2
  have hcm := sourceCanonicalRootDomain_of_enclosingCircle hp hp1 φ m
    cm.spectralCenter cm.spectralRadius hgm.1 hgm.2
  have hin := circleIntegrable_sourceActionVariationCotangent hp hp1 φ
    cn.spectralCenter cn.spectralRadius cn.spectralRadius_pos.le hcn
  have him := circleIntegrable_sourceActionVariationCotangent hp hp1 φ
    cm.spectralCenter cm.spectralRadius cm.spectralRadius_pos.le hcm
  rw [sourceBracket,
    fderiv_sourceComplexAction_eq_cotangent_circle_on_chart hp hp1 n cn φ hreal hn,
    fderiv_sourceComplexAction_eq_cotangent_circle_on_chart hp hp1 m cm φ hreal hm]
  simp only [map_smul,smul_apply,smul_eq_mul]
  rw [bilinear_circleIntegral (sourceBivector h2p) hin him]
  ring

/-- The literal scalar kernel is the Poisson bracket of discriminants
at the two spectral parameters, divided by their canonical roots. -/
theorem sourceBracket_actions_eq_discriminant_double_circle
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2:ℝ≥0∞) ≤ p) (n m : ℤ)
    (cn : SourceRealActionBallChart hp hp1 n) (cm : SourceRealActionBallChart hp hp1 m)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ))
    (hn : φ ∈ ball cn.center cn.radius) (hm : φ ∈ ball cm.center cm.radius) :
    sourceBracket h2p (sourceComplexAction hp hp1 n) (sourceComplexAction hp hp1 m) φ =
      ((Real.pi : ℂ)⁻¹)^2*
        (∮ z in C(cn.spectralCenter,cn.spectralRadius),
          ∮ w in C(cm.spectralCenter,cm.spectralRadius),
            (sourceCanonicalRoot hp hp1 φ z)⁻¹*(sourceCanonicalRoot hp hp1 φ w)⁻¹*
              sourceBracket h2p
                (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ) z)
                (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ) w) φ) := by
  rw [sourceBracket_actions_eq_double_circle hp hp1 h2p n m cn cm φ hreal hn hm]
  congr 1
  apply circleIntegral.integral_congr cn.spectralRadius_pos.le
  intro z _
  dsimp only
  apply circleIntegral.integral_congr cm.spectralRadius_pos.le
  intro w _
  dsimp only
  exact sourceBivector_actionVariationCotangents_eq_discriminant_bracket hp hp1 h2p φ z w

/-- Only commutation on the two selected spectral circles is needed
to deduce the actual action-action zero bracket. -/
theorem sourceBracket_actions_eq_zero_of_discriminant_commutes_on_circles
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2:ℝ≥0∞) ≤ p) (n m : ℤ)
    (cn : SourceRealActionBallChart hp hp1 n) (cm : SourceRealActionBallChart hp hp1 m)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ))
    (hn : φ ∈ ball cn.center cn.radius) (hm : φ ∈ ball cm.center cm.radius)
    (hcomm : ∀ z ∈ sphere cn.spectralCenter cn.spectralRadius,
      ∀ w ∈ sphere cm.spectralCenter cm.spectralRadius,
        sourceBracket h2p
          (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ) z)
          (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ) w) φ = 0) :
    sourceBracket h2p (sourceComplexAction hp hp1 n) (sourceComplexAction hp hp1 m) φ = 0 := by
  rw [sourceBracket_actions_eq_double_circle hp hp1 h2p n m cn cm φ hreal hn hm]
  have hinner (z : ℂ) (hz : z ∈ sphere cn.spectralCenter cn.spectralRadius) :
      (∮ w in C(cm.spectralCenter,cm.spectralRadius),
        sourceBivector h2p (sourceActionVariationCotangent hp hp1 φ z)
          (sourceActionVariationCotangent hp hp1 φ w)) = 0 := by
    calc
      _ = ∮ w in C(cm.spectralCenter,cm.spectralRadius), (0 : ℂ) := by
        apply circleIntegral.integral_congr cm.spectralRadius_pos.le
        intro w hw
        dsimp only
        rw [sourceBivector_actionVariationCotangents_eq_discriminant_bracket,
          hcomm z hz w hw,mul_zero]
      _ = 0 := by simp [circleIntegral]
  have houter : (∮ z in C(cn.spectralCenter,cn.spectralRadius),
      ∮ w in C(cm.spectralCenter,cm.spectralRadius),
        sourceBivector h2p (sourceActionVariationCotangent hp hp1 φ z)
          (sourceActionVariationCotangent hp hp1 φ w)) = 0 := by
    calc
      _ = ∮ z in C(cn.spectralCenter,cn.spectralRadius), (0 : ℂ) :=
        circleIntegral.integral_congr cn.spectralRadius_pos.le hinner
      _ = 0 := by simp [circleIntegral]
  rw [houter,mul_zero]

theorem sourceBracket_actions_eq_zero_of_discriminant_commutes
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2:ℝ≥0∞) ≤ p)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ))
    (hcomm : ∀ z w : ℂ, sourceBracket h2p
      (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ) z)
      (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ) w) φ = 0)
    (n m : ℤ) :
    sourceBracket h2p (sourceComplexAction hp hp1 n) (sourceComplexAction hp hp1 m) φ = 0 := by
  obtain ⟨cn,hcn⟩ := exists_sourceRealActionBallChart_centered hp hp1 n φ hreal
  obtain ⟨cm,hcm⟩ := exists_sourceRealActionBallChart_centered hp hp1 m φ hreal
  apply sourceBracket_actions_eq_zero_of_discriminant_commutes_on_circles hp hp1 h2p n m cn cm φ hreal
    (by rw [hcn]; exact mem_ball_self cn.radius_pos)
    (by rw [hcm]; exact mem_ball_self cm.radius_pos)
  exact fun z _ w _ => hcomm z w

end NLS.ZakharovShabat
