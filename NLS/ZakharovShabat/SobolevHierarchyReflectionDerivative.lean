import NLS.ZakharovShabat.SobolevHierarchyReflectionIntegral
import NLS.FunctionalAnalysis.CurveL2IntegralGraph

/-! # Actual spatial differentiation of the sharp Sobolev nonlocal recurrence -/
noncomputable section
open Set Complex Filter Topology MeasureTheory NLS.Fourier NLS.LinearVolterra NLS.FunctionalAnalysis
namespace NLS.ZakharovShabat

def hierarchyPhysicalGradient (s k : ℕ) (ab : SobolevSource s) (x : ℝ) : ℂ × ℂ :=
  ((sobolevNLSHierarchyContinuousGradient s k ab).1 (x : AddCircle (2:ℝ)),
   (sobolevNLSHierarchyContinuousGradient s k ab).2 (x : AddCircle (2:ℝ)))

theorem hierarchyPhysicalGradient_represents (s k : ℕ) (hs : 1 ≤ s) (hk : k ≤ s) (ab : SobolevSource s) :
    (fun x => (unitL2SynthesisEquiv (sobolevNLSHierarchyGradient s k ab).1 x,
      unitL2SynthesisEquiv (sobolevNLSHierarchyGradient s k ab).2 x))
      =ᵐ[volume.restrict (Ioc 0 1)] hierarchyPhysicalGradient s k ab := by
  rw [← sobolevNLSHierarchyContinuousGradient_coefficients s k hs hk ab]
  have h₁ := circle_ae_pullback (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) AddCircle.haarAddCircle
    (sobolevNLSHierarchyContinuousGradient s k ab).1)
  have h₂ := circle_ae_pullback (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) AddCircle.haarAddCircle
    (sobolevNLSHierarchyContinuousGradient s k ab).2)
  have hsub : Ioc (0:ℝ) 1 ⊆ Ioc 0 2 := Ioc_subset_Ioc_right (by norm_num)
  filter_upwards [unitL2Synthesis_circleUnitCoefficients
    (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (sobolevNLSHierarchyContinuousGradient s k ab).1),
    unitL2Synthesis_circleUnitCoefficients
      (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (sobolevNLSHierarchyContinuousGradient s k ab).2),
    ae_restrict_of_ae_restrict_of_subset hsub h₁,ae_restrict_of_ae_restrict_of_subset hsub h₂]
      with x hx₁ hx₂ hxC₁ hxC₂
  exact Prod.ext (hx₁.trans hxC₁) (hx₂.trans hxC₂)

theorem sobolevNLSHierarchyCircleGradient_represents (s k : ℕ) (hs : 1 ≤ s) (ab : SobolevSource s) :
    (fun x => (unitL2SynthesisEquiv (sobolevNLSHierarchyGradient s k ab).1 x,
      unitL2SynthesisEquiv (sobolevNLSHierarchyGradient s k ab).2 x))
      =ᵐ[volume.restrict (Ioc 0 1)]
        (fun x => (circlePullback (sobolevNLSHierarchyCircleGradient s k ab).1 x,
          circlePullback (sobolevNLSHierarchyCircleGradient s k ab).2 x)) := by
  filter_upwards [unitL2Synthesis_circleUnitCoefficients (sobolevNLSHierarchyCircleGradient s k ab).1,
    unitL2Synthesis_circleUnitCoefficients (sobolevNLSHierarchyCircleGradient s k ab).2] with x hx₁ hx₂
  simpa only [sobolevNLSHierarchyGradient,dif_pos hs,sobolevNLSHierarchyCircleGradient] using Prod.ext hx₁ hx₂

theorem hierarchyReflection_unit_regular
    (m : ℕ) (ε : ℂ) (hε : ε=1 ∨ ε = -1) (ab : SobolevSource (2*m+1))
    (hT : hierarchyMidpointReflection (2*m+1) ab=ε • ab) :
    AbsolutelyContinuousOnInterval (extend (hierarchyUnitGradient (2*m+1) (2*m+1) ab).1) 0 1 ∧
    AbsolutelyContinuousOnInterval (extend (hierarchyUnitGradient (2*m+1) (2*m+1) ab).2) 0 1 ∧
    ∀ᵐ x ∂volume.restrict (Ioc (0:ℝ) 1),
      HasDerivAt (fun y => (extend (hierarchyUnitGradient (2*m+1) (2*m+1) ab).1 y,
        extend (hierarchyUnitGradient (2*m+1) (2*m+1) ab).2 y))
        (I*circlePullback (sobolevNLSHierarchyCircleGradient (2*m+1) (2*m+2) ab).1 x-
          (2*I)*extend ((hierarchyUnitPotential (2*m+1) ab).2*hierarchyNonlocalPrimitive (2*m+1) (2*m+1) ab) x,
         -I*circlePullback (sobolevNLSHierarchyCircleGradient (2*m+1) (2*m+2) ab).2 x-
          (2*I)*extend (-((hierarchyUnitPotential (2*m+1) ab).1*hierarchyNonlocalPrimitive (2*m+1) (2*m+1) ab)) x) x := by
  have h₁ := unitCurve_regular_of_L2_integral_graph
    (hierarchyUnitGradient (2*m+1) (2*m+1) ab).1
    ((hierarchyUnitPotential (2*m+1) ab).2*hierarchyNonlocalPrimitive (2*m+1) (2*m+1) ab)
    (sobolevNLSHierarchyCircleGradient (2*m+1) (2*m+2) ab).1 I (-(2*I)) (by
      intro t
      have h := congrArg Prod.fst (hierarchyFTC_eq_of_reflection m ε hε ab hT t)
      simpa only [hierarchyFTCLeft,hierarchyFTCRight,hierarchyIntegratedNonlocal,sub_eq_add_neg,neg_mul] using h)
  have h₂ := unitCurve_regular_of_L2_integral_graph
    (hierarchyUnitGradient (2*m+1) (2*m+1) ab).2
    (-((hierarchyUnitPotential (2*m+1) ab).1*hierarchyNonlocalPrimitive (2*m+1) (2*m+1) ab))
    (sobolevNLSHierarchyCircleGradient (2*m+1) (2*m+2) ab).2 (-I) (-(2*I)) (by
      intro t
      have h := congrArg Prod.snd (hierarchyFTC_eq_of_reflection m ε hε ab hT t)
      simpa only [hierarchyFTCLeft,hierarchyFTCRight,hierarchyIntegratedNonlocal,sub_eq_add_neg,neg_mul] using h)
  refine ⟨h₁.1,h₂.1,?_⟩
  filter_upwards [h₁.2,h₂.2] with x hx₁ hx₂
  simpa only [sub_eq_add_neg,neg_mul] using hx₁.prodMk hx₂

/-- Every original H^(2m+1) reflected input has the actual derivative of
the physical continuous lower gradient, with the original L2 upper gradient. -/
theorem hierarchyReflection_physical_hasDerivAt
    (m : ℕ) (ε : ℂ) (hε : ε=1 ∨ ε = -1) (ab : SobolevSource (2*m+1))
    (hT : hierarchyMidpointReflection (2*m+1) ab=ε • ab) :
    ∀ᵐ x ∂volume.restrict (Ioc (0:ℝ) 1),
      HasDerivAt (hierarchyPhysicalGradient (2*m+1) (2*m+1) ab)
        (I*unitL2SynthesisEquiv (sobolevNLSHierarchyGradient (2*m+1) (2*m+2) ab).1 x-
          (2*I)*extend ((hierarchyUnitPotential (2*m+1) ab).2*hierarchyNonlocalPrimitive (2*m+1) (2*m+1) ab) x,
         -I*unitL2SynthesisEquiv (sobolevNLSHierarchyGradient (2*m+1) (2*m+2) ab).2 x-
          (2*I)*extend (-((hierarchyUnitPotential (2*m+1) ab).1*hierarchyNonlocalPrimitive (2*m+1) (2*m+1) ab)) x) x := by
  filter_upwards [(hierarchyReflection_unit_regular m ε hε ab hT).2.2,
    sobolevNLSHierarchyCircleGradient_represents (2*m+1) (2*m+2) (by omega) ab,
    ae_restrict_mem measurableSet_Ioc,
    ae_restrict_of_ae (show ∀ᵐ x : ℝ, x ≠ (1:ℝ) from by simp [ae_iff,measure_singleton])]
      with x hxd hxr hx hx1
  have hr₁ := congrArg Prod.fst hxr
  have hr₂ := congrArg Prod.snd hxr
  dsimp only at hr₁ hr₂
  rw [← hr₁,← hr₂] at hxd
  apply hxd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hx.1 (lt_of_le_of_ne hx.2 hx1)] with y hy
  rw [extend_coe _ ⟨y,hy.1.le,hy.2.le⟩,extend_coe _ ⟨y,hy.1.le,hy.2.le⟩]
  rfl

end NLS.ZakharovShabat
