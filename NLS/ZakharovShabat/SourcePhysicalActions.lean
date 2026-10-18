import NLS.ZakharovShabat.SourcePhysicalRealL2
import NLS.ZakharovShabat.L2DiscriminantCotangent
import NLS.ZakharovShabat.SourceActionPiecewiseContour
import NLS.ZakharovShabat.SourceIndexedActionAnalytic
import NLS.ZakharovShabat.SourcePsiFree

/-! # Actual physical Hilbert actions

The original spectral labels and canonical product are transported through
the exact Fourier equivalence. The resulting actions are literal integrals
of the actual L2 monodromy discriminant, with its spectral derivative.
Real sources supply non-singular isolating circles even at collapsed gaps.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The canonical product root on a physical L2 input, with the original frequency labels. -/
def physicalCanonicalRoot (u : IntervalPairL2) (z : ℂ) : ℂ :=
  sourceCanonicalRoot (by simp) (by norm_num) (sourcePhysicalL2Equiv.symm u) z

/-- The indexed action on the physical input, using its actual Fourier coefficients. -/
def physicalIndexedAction (n : ℤ) (u : IntervalPairL2) : ℂ :=
  sourceIndexedAction (by simp) (by norm_num) n (sourcePhysicalL2Equiv.symm u)

/-- The literal normalized contour integral uses the actual physical monodromy discriminant. -/
def physicalActionContour (u : IntervalPairL2) (Γ : PiecewiseC1Loop) : ℂ :=
  (Real.pi : ℂ)⁻¹*Γ.integral (fun z => z*deriv (l2Discriminant u) z/physicalCanonicalRoot u z)

/-- The free physical root has the original negative sign, not an unspecified square root. -/
theorem physicalCanonicalRoot_zero (z : ℂ) : physicalCanonicalRoot 0 z = -2*I*sin z := by
  rw [physicalCanonicalRoot,map_zero]
  exact sourceCanonicalRoot_zero_source_eq_free_sine (by simp) (by norm_num) 0 z

/-- The canonical physical product squares to the actual L2 discriminant squared minus four. -/
theorem physicalCanonicalRoot_sq (u : IntervalPairL2) (z : ℂ)
    (hz : z ∈ sourceCanonicalRootDomain (by simp) (by norm_num) (sourcePhysicalL2Equiv.symm u)) :
    physicalCanonicalRoot u z ^ 2 = l2Discriminant u z ^ 2-4 := by
  rw [physicalCanonicalRoot,sourceCanonicalRoot_sq_eq_discriminant_sq_sub_four (by simp) (by norm_num)
    _ _ hz,canonicalDiscriminant_eq_l2_source,sourcePhysicalL2_equiv_symm]

/-- The physical monodromy integral equals the original coefficient-source contour integral. -/
theorem physicalActionContour_eq (u : IntervalPairL2) (Γ : PiecewiseC1Loop) :
    physicalActionContour u Γ =
      sourceActionContour (by simp) (by norm_num) (sourcePhysicalL2Equiv.symm u) Γ := by
  simp only [physicalActionContour,sourceActionContour,sourceCriticalRootRatioJoint,
    deriv_canonicalDiscriminant_eq_l2,sourcePhysicalL2_equiv_symm,physicalCanonicalRoot,mul_div_assoc]

/-- Every original isolating circle computes the actual physical spectral action. -/
theorem physicalIndexedAction_eq_circle (u : IntervalPairL2) (n : ℤ)
    (C : SourceCriticalRootPeriodCircle (by simp) (by norm_num) (sourcePhysicalL2Equiv.symm u) n) :
    physicalIndexedAction n u = (Real.pi : ℂ)⁻¹ *
      ∮ z in C((C.center : ℂ),C.radius), z*deriv (l2Discriminant u) z/physicalCanonicalRoot u z := by
  rw [physicalIndexedAction,sourceIndexedAction_eq_circle C]
  simp only [sourceActionCircle,sourceCriticalRootRatioJoint,deriv_canonicalDiscriminant_eq_l2,
    sourcePhysicalL2_equiv_symm,physicalCanonicalRoot,mul_div_assoc]

/-- Every admissible winding-one circuit computes the same physical action. -/
theorem physicalIndexedAction_eq_circuit (u : IntervalPairL2) (n : ℤ)
    (C : SourceCriticalRootPeriodCircle (by simp) (by norm_num) (sourcePhysicalL2Equiv.symm u) n)
    (Γ : PiecewiseC1Loop)
    (hΓ : Γ.Inside (ball (C.center : ℂ) C.radius \
      sourcePeriodicSegment (by simp) (by norm_num) (sourcePhysicalL2Equiv.symm u) n))
    (hw : Γ.windingIntegral (canonicalPeriodicMidpoint (by simp) (by norm_num)
      (periodOnePotential (sourcePhysicalL2Equiv.symm u)) (periodOnePotential_mem _) n) = 1) :
    physicalIndexedAction n u = physicalActionContour u Γ := by
  rw [physicalActionContour_eq,C.actionContour_eq_mul_winding Γ hΓ,hw,mul_one]
  rfl

/-- Every physical real action is real and nonnegative, including collapsed gaps. -/
theorem physicalIndexedAction_nonneg (u : physicalRealSubmodule) (n : ℤ) :
    0 ≤ (physicalIndexedAction n u.val).re ∧ (physicalIndexedAction n u.val).im = 0 :=
  ⟨(sourceIndexedAction_nonneg_and_eq_zero_iff_gap_zero (by simp) (by norm_num)
    n (sourcePhysicalL2Equiv.symm u.val) u.property).1,
   (sourceIndexedAction_nonneg_and_eq_zero_iff_gap_zero (by simp) (by norm_num)
    n (sourcePhysicalL2Equiv.symm u.val) u.property).2.1⟩

/-- Real physical inputs supply actual non-singular action circles, including collapsed gaps. -/
theorem exists_physicalIndexedAction_circle (u : physicalRealSubmodule) (n : ℤ) :
    ∃ c r : ℝ, 0 < r ∧
      (∀ z ∈ sphere (c : ℂ) r, physicalCanonicalRoot u.val z ≠ 0 ∧
        physicalCanonicalRoot u.val z^2 = l2Discriminant u.val z^2-4) ∧
      physicalIndexedAction n u.val = (Real.pi : ℂ)⁻¹ *
        ∮ z in C((c : ℂ),r), z*deriv (l2Discriminant u.val) z/physicalCanonicalRoot u.val z := by
  let φ := sourcePhysicalL2Equiv.symm u.val
  obtain ⟨N,ε,_,_,V,_,_,hφV,c,hD⟩ :=
    exists_local_source_quantitative_isolating_discs (by simp) (by norm_num) φ u.property
  obtain ⟨a,r,hr,he⟩ := hD.discs n
  let C := hD.periodCircle φ hφV n a r hr he
  refine ⟨C.center,C.radius,C.radius_pos,?_,physicalIndexedAction_eq_circle u.val n C⟩
  intro z hz
  exact ⟨sourceCanonicalRoot_ne_zero_off_gaps (by simp) (by norm_num) φ z
    (C.sphere_subset_rootDomain hz),physicalCanonicalRoot_sq u.val z (C.sphere_subset_rootDomain hz)⟩

end NLS.ZakharovShabat
