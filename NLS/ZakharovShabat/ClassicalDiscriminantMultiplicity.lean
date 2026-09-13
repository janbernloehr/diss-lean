import NLS.ZakharovShabat.ClassicalBoundaryMultiplicity
import NLS.ZakharovShabat.ClassicalMonodromyAnalytic
import NLS.ZakharovShabat.CanonicalParityProducts

/-!
# Classical discriminant orders and canonical spectral products

The shifted trace functions have the original even and odd algebraic
multiplicities. Their product has the full periodic multiplicity. Thus the
classical functions and the canonical products agree in all vanishing orders;
entire-function normalization remains a separate step.
-/

noncomputable section
open Set Complex Matrix MeasureTheory NLS.Fourier NLS.LinearVolterra
open scoped Matrix.Norms.Elementwise
namespace NLS.ZakharovShabat

/-- The trace minus two has precisely the original even-sector multiplicity. -/
theorem analyticOrderAt_classicalDiscriminant_sub_two
    (φ : PairSpace 2) (hφ : φ ∈ pairParitySubspace 0)
    (Φ : Curve (ℂ × ℂ)) (hΦ : physicalBase φ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (z : ℂ) : analyticOrderAt (fun w => classicalDiscriminant Φ w-2) z =
      (parityAlgebraicMultiplicity (by simp) φ 0 z : ℕ∞) := by
  have h := analyticOrderAt_classicalBoundaryDeterminant φ hφ Φ hΦ z 0
  have he : (fun w => (classicalMonodromy Φ w-wave 0 1 • 1).det) =
      -(fun w => classicalDiscriminant Φ w-2) := by
    funext w
    rw [det_classicalMonodromy_sub_scalar,wave_zero]
    simp
    ring
  rw [he,analyticOrderAt_neg] at h
  exact h

/-- The trace plus two has precisely the original odd-sector multiplicity. -/
theorem analyticOrderAt_classicalDiscriminant_add_two
    (φ : PairSpace 2) (hφ : φ ∈ pairParitySubspace 0)
    (Φ : Curve (ℂ × ℂ)) (hΦ : physicalBase φ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (z : ℂ) : analyticOrderAt (fun w => classicalDiscriminant Φ w+2) z =
      (parityAlgebraicMultiplicity (by simp) φ 1 z : ℕ∞) := by
  have h := analyticOrderAt_classicalBoundaryDeterminant φ hφ Φ hΦ z 1
  have hw : wave 1 1 = -1 := by simpa using wave_odd_at_one 0
  have he : (fun w => (classicalMonodromy Φ w-wave 1 1 • 1).det) =
      fun w => classicalDiscriminant Φ w+2 := by
    funext w
    rw [det_classicalMonodromy_sub_scalar,hw]
    ring
  rw [he] at h
  exact h

/-- The trace squared minus four has precisely the full original periodic multiplicity. -/
theorem analyticOrderAt_classicalDiscriminant_sq_sub_four
    (φ : PairSpace 2) (hφ : φ ∈ pairParitySubspace 0)
    (Φ : Curve (ℂ × ℂ)) (hΦ : physicalBase φ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (z : ℂ) : analyticOrderAt (fun w => (classicalDiscriminant Φ w)^2-4) z =
      (periodicAlgebraicMultiplicity (by simp) φ z : ℕ∞) := by
  have hpair : AnalyticAt ℂ (fun w : ℂ => (w,Φ)) z := analyticAt_id.prod analyticAt_const
  have hΔ : AnalyticAt ℂ (classicalDiscriminant Φ) z :=
    (analyticOnNhd_classicalDiscriminant_joint (z,Φ) (mem_univ _)).comp (f := fun w : ℂ => (w,Φ)) hpair
  have he : (fun w => (classicalDiscriminant Φ w)^2-4) =
      (fun w => classicalDiscriminant Φ w-2)*(fun w => classicalDiscriminant Φ w+2) := by
    funext w
    simp only [Pi.mul_apply]
    ring
  have hs : AnalyticAt ℂ (fun w => classicalDiscriminant Φ w-2) z := hΔ.sub analyticAt_const
  have ha : AnalyticAt ℂ (fun w => classicalDiscriminant Φ w+2) z := hΔ.add analyticAt_const
  rw [he,analyticOrderAt_mul hs ha,
    analyticOrderAt_classicalDiscriminant_sub_two φ hφ Φ hΦ,
    analyticOrderAt_classicalDiscriminant_add_two φ hφ Φ hΦ,
    periodicAlgebraicMultiplicity_eq_parity_sum (by simp) φ hφ,ENat.natCast_add]

/-- Intrinsic parity products and classical parity determinants have equal orders at every point. -/
theorem analyticOrderAt_canonicalParity_eq_classicalBoundary
    (φ : PairSpace 2) (hφ : φ ∈ pairParitySubspace 0)
    (Φ : Curve (ℂ × ℂ)) (hΦ : physicalBase φ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (r : ℤ) (hr : r = 0 ∨ r = 1) (z : ℂ) :
    analyticOrderAt (canonicalParityProduct (by simp) φ r) z =
      analyticOrderAt (fun w => (classicalMonodromy Φ w-wave r 1 • 1).det) z := by
  rw [analyticOrderAt_classicalBoundaryDeterminant φ hφ Φ hΦ]
  exact ((canonicalParityProduct_spec (by simp) (by norm_num) φ hφ r hr).2 z).1

/-- The canonical even product and trace minus two have equal orders everywhere. -/
theorem analyticOrderAt_canonicalEven_eq_classicalDiscriminant_sub_two
    (φ : PairSpace 2) (hφ : φ ∈ pairParitySubspace 0)
    (Φ : Curve (ℂ × ℂ)) (hΦ : physicalBase φ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (z : ℂ) : analyticOrderAt (canonicalParityProduct (by simp) φ 0) z =
      analyticOrderAt (fun w => classicalDiscriminant Φ w-2) z := by
  rw [analyticOrderAt_classicalDiscriminant_sub_two φ hφ Φ hΦ]
  exact ((canonicalParityProduct_spec (by simp) (by norm_num) φ hφ 0 (Or.inl rfl)).2 z).1

/-- The canonical odd product and trace plus two have equal orders everywhere. -/
theorem analyticOrderAt_canonicalOdd_eq_classicalDiscriminant_add_two
    (φ : PairSpace 2) (hφ : φ ∈ pairParitySubspace 0)
    (Φ : Curve (ℂ × ℂ)) (hΦ : physicalBase φ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (z : ℂ) : analyticOrderAt (canonicalParityProduct (by simp) φ 1) z =
      analyticOrderAt (fun w => classicalDiscriminant Φ w+2) z := by
  rw [analyticOrderAt_classicalDiscriminant_add_two φ hφ Φ hΦ]
  exact ((canonicalParityProduct_spec (by simp) (by norm_num) φ hφ 1 (Or.inr rfl)).2 z).1

/-- The canonical full product and trace squared minus four have equal orders everywhere. -/
theorem analyticOrderAt_canonicalPeriodic_eq_classicalDiscriminant_sq_sub_four
    (φ : PairSpace 2) (hφ : φ ∈ pairParitySubspace 0)
    (Φ : Curve (ℂ × ℂ)) (hΦ : physicalBase φ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (z : ℂ) : analyticOrderAt (canonicalPeriodicProduct (by simp) φ) z =
      analyticOrderAt (fun w => (classicalDiscriminant Φ w)^2-4) z := by
  rw [analyticOrderAt_classicalDiscriminant_sq_sub_four φ hφ Φ hΦ]
  exact analyticOrderAt_canonicalPeriodicProduct (by simp) (by norm_num) φ z

end NLS.ZakharovShabat
