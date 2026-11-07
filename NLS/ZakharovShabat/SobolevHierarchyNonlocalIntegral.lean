import NLS.ZakharovShabat.SobolevHierarchyNonlocalFields
import NLS.ZakharovShabat.NLSHierarchyNonlocalRecurrence

/-! # Exact zero-initial nonlocal integrals of the native continuous fields -/
noncomputable section
open Set Complex MeasureTheory NLS.Fourier NLS.LinearVolterra NLS.FunctionalAnalysis
open scoped ContDiff
namespace NLS.ZakharovShabat

theorem hierarchyNonlocalPrimitive_eq_physical (s k : ℕ) (ab : SobolevSource s) (t : Icc (0:ℝ) 1) :
    hierarchyNonlocalPrimitive s k ab t =
      ∫ y in (0:ℝ)..t.val, extend (hierarchyRPairingCurve s k ab) y :=
  unitComplexCurvePrimitive_apply _ t

theorem hierarchyNonlocalPrimitive_eq_classical
    (s k : ℕ) (hs : 1 ≤ s) (hk : k ≤ s) (ab : SobolevSource s) (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1)
    (haq : ∀ j, ab.1.val j = periodOneCoefficient a j)
    (hbq : ∀ j, ab.2.val j = periodOneCoefficient b j) (t : Icc (0:ℝ) 1) :
    hierarchyNonlocalPrimitive s k ab t =
      ∫ y in (0:ℝ)..t.val, classicalNLSHierarchyRPairing a b k y := by
  rw [hierarchyNonlocalPrimitive_eq_physical]
  apply intervalIntegral.integral_congr
  intro y hy
  have hyt : y ∈ Icc (0:ℝ) 1 := by
    rw [uIcc_of_le t.property.1] at hy
    exact ⟨hy.1,hy.2.trans t.property.2⟩
  rw [extend_coe _ ⟨y,hyt⟩]
  have hU := hierarchyUnitPotential_eq_classical s hs ab a b ha hb hpa hpb haq hbq ⟨y,hyt⟩
  have hG := hierarchyUnitGradient_eq_classical s k hs hk ab a b ha hb hpa hpb haq hbq ⟨y,hyt⟩
  have hU₁ := congrArg Prod.fst hU
  have hU₂ := congrArg Prod.snd hU
  have hG₁ := congrArg Prod.fst hG
  have hG₂ := congrArg Prod.snd hG
  dsimp only at hU₁ hU₂ hG₁ hG₂
  change I*((hierarchyUnitPotential s ab).1 ⟨y,hyt⟩*(hierarchyUnitGradient s k ab).1 ⟨y,hyt⟩)-
    I*((hierarchyUnitPotential s ab).2 ⟨y,hyt⟩*(hierarchyUnitGradient s k ab).2 ⟨y,hyt⟩) = _
  rw [hU₁,hU₂,hG₁,hG₂]
  unfold classicalNLSHierarchyRPairing
  ring

theorem hierarchyIntegratedNonlocal_eq_classical
    (s k : ℕ) (hs : 1 ≤ s) (hk : k ≤ s) (ab : SobolevSource s) (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1)
    (haq : ∀ j, ab.1.val j = periodOneCoefficient a j)
    (hbq : ∀ j, ab.2.val j = periodOneCoefficient b j) (t : Icc (0:ℝ) 1) :
    ((hierarchyIntegratedNonlocal s k ab).1 t,(hierarchyIntegratedNonlocal s k ab).2 t) =
      ((∫ y in (0:ℝ)..t.val, b y*(∫ z in (0:ℝ)..y, classicalNLSHierarchyRPairing a b k z)),
       (∫ y in (0:ℝ)..t.val, -(a y*(∫ z in (0:ℝ)..y, classicalNLSHierarchyRPairing a b k z)))) := by
  have hU := hierarchyUnitPotential_eq_classical s hs ab a b ha hb hpa hpb haq hbq
  have hN := hierarchyNonlocalPrimitive_eq_classical s k hs hk ab a b ha hb hpa hpb haq hbq
  apply Prod.ext
  · change unitComplexCurvePrimitive _ t = _
    rw [unitComplexCurvePrimitive_apply]
    apply intervalIntegral.integral_congr
    intro y hy
    have hyt : y ∈ Icc (0:ℝ) 1 := by
      rw [uIcc_of_le t.property.1] at hy
      exact ⟨hy.1,hy.2.trans t.property.2⟩
    rw [extend_coe _ ⟨y,hyt⟩]
    change (hierarchyUnitPotential s ab).2 ⟨y,hyt⟩*hierarchyNonlocalPrimitive s k ab ⟨y,hyt⟩ = _
    rw [hN]
    exact congrArg (fun c : ℂ => c*_) (congrArg Prod.snd (hU ⟨y,hyt⟩))
  · change unitComplexCurvePrimitive _ t = _
    rw [unitComplexCurvePrimitive_apply]
    apply intervalIntegral.integral_congr
    intro y hy
    have hyt : y ∈ Icc (0:ℝ) 1 := by
      rw [uIcc_of_le t.property.1] at hy
      exact ⟨hy.1,hy.2.trans t.property.2⟩
    rw [extend_coe _ ⟨y,hyt⟩]
    change -((hierarchyUnitPotential s ab).1 ⟨y,hyt⟩*hierarchyNonlocalPrimitive s k ab ⟨y,hyt⟩) = _
    rw [hN]
    exact congrArg (fun c : ℂ => -(c*_)) (congrArg Prod.fst (hU ⟨y,hyt⟩))

theorem circlePrimitive_eq_of_ae_unit (f : CircleL2) (g : ℝ → ℂ)
    (h : circlePullback f =ᵐ[volume.restrict (Ioc 0 1)] g) (t : Icc (0:ℝ) 1) :
    circlePrimitive t.val f = ∫ y in (0:ℝ)..t.val, g y := by
  unfold circlePrimitive
  rw [intervalIntegral.integral_of_le t.property.1,intervalIntegral.integral_of_le t.property.1]
  exact integral_congr_ae (ae_restrict_of_ae_restrict_of_subset
    (Ioc_subset_Ioc le_rfl t.property.2) h)

end NLS.ZakharovShabat
