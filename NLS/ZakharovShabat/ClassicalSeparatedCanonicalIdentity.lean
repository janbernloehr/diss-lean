import NLS.ZakharovShabat.ClassicalSeparatedPhysicalReconstruction
import NLS.ZakharovShabat.ClassicalSeparatedExteriorBounds
import NLS.ZakharovShabat.ClassicalSeparatedHalfPlaneAsymptotics
import NLS.ZakharovShabat.EntireFreeDiscBounds
import NLS.ComplexAnalysis.EqualOrderQuotient
import NLS.ComplexAnalysis.CommonNormalizationLimits

/-!
# Exact normalization of the classical separated characteristics

The classical endpoint characteristic and the intrinsic product have equal
orders at every spectral parameter. Their filled quotient is entire and
nonzero. Exterior bounds, maximum modulus, and the upper normalization fix
this factor to one.
-/

noncomputable section
open Set Complex Filter Topology MeasureTheory NLS.LinearVolterra NLS.Fourier
open NLS.ComplexAnalysis
namespace NLS.ZakharovShabat
open BoundaryCondition

/-- The monodromy endpoint characteristic is entire in the spectral variable. -/
theorem analyticOnNhd_classicalSeparatedCharacteristic
    (b : BoundaryCondition) (Φ : Curve (ℂ × ℂ)) :
    AnalyticOnNhd ℂ (classicalSeparatedCharacteristic b Φ) univ := by
  intro z _
  have hpair : AnalyticAt ℂ (fun w : ℂ => (w,Φ)) z :=
    analyticAt_id.prod analyticAt_const
  exact ((analyticOnNhd_classicalSeparatedCharacteristic_joint b
    (z,Φ) (mem_univ _)).comp (f := fun w : ℂ => (w,Φ)) hpair)

/-- The classical and intrinsic boundary functions have the same order at
every point, including multiple eigenvalues. -/
theorem analyticOrderAt_classicalSeparated_eq_characteristic
    (b : BoundaryCondition) (Φ : Curve (ℂ × ℂ))
    (hΦ : MemLp (extend Φ) 2 (volume.restrict (Ioc 0 1))) (z : ℂ) :
    analyticOrderAt (classicalSeparatedCharacteristic b Φ) z =
      analyticOrderAt (b.characteristic (by simp)
        (intervalPotentialCoefficients (intervalL2OfFunction (extend Φ) hΦ))
        (intervalPotentialCoefficients_mem _) ) z := by
  rw [analyticOrderAt_classicalSeparated_eq_physicalMultiplicity b Φ hΦ z,
    b.analyticOrderAt_characteristic (by simp) (by norm_num)]
  exact_mod_cast (b.classicalAlgebraicMultiplicity_eq
    (intervalL2OfFunction (extend Φ) hΦ) z)

/-- Removable common zeros are filled by one entire normalization factor. -/
def classicalSeparatedProductQuotient (b : BoundaryCondition)
    (Φ : Curve (ℂ × ℂ)) (hΦ : MemLp (extend Φ) 2 (volume.restrict (Ioc 0 1))) :
    ℂ → ℂ :=
  analyticQuotient (classicalSeparatedCharacteristic b Φ)
    (b.characteristic (by simp)
      (intervalPotentialCoefficients (intervalL2OfFunction (extend Φ) hΦ))
      (intervalPotentialCoefficients_mem _))

theorem analyticOnNhd_classicalSeparatedProductQuotient
    (b : BoundaryCondition) (Φ : Curve (ℂ × ℂ))
    (hΦ : MemLp (extend Φ) 2 (volume.restrict (Ioc 0 1))) :
    AnalyticOnNhd ℂ (classicalSeparatedProductQuotient b Φ hΦ) univ := by
  apply analyticOnNhd_analyticQuotient
    (analyticOnNhd_classicalSeparatedCharacteristic b Φ)
    (b.analyticOnNhd_characteristic (by simp) (by norm_num)
      _ (intervalPotentialCoefficients_mem _))
    (analyticOrderAt_classicalSeparated_eq_characteristic b Φ hΦ)
  intro z
  rw [b.analyticOrderAt_characteristic (by simp) (by norm_num)]
  exact ENat.natCast_ne_top _

theorem classicalSeparatedProductQuotient_mul
    (b : BoundaryCondition) (Φ : Curve (ℂ × ℂ))
    (hΦ : MemLp (extend Φ) 2 (volume.restrict (Ioc 0 1))) (z : ℂ) :
    classicalSeparatedProductQuotient b Φ hΦ z *
      b.characteristic (by simp)
        (intervalPotentialCoefficients (intervalL2OfFunction (extend Φ) hΦ))
        (intervalPotentialCoefficients_mem _) z =
      classicalSeparatedCharacteristic b Φ z :=
  analyticQuotient_mul (analyticOnNhd_classicalSeparatedCharacteristic b Φ)
    (b.analyticOnNhd_characteristic (by simp) (by norm_num)
      _ (intervalPotentialCoefficients_mem _))
    (analyticOrderAt_classicalSeparated_eq_characteristic b Φ hΦ) z

/-- The filled quotient is globally bounded: exterior estimates propagate
through every free disc by maximum modulus. -/
theorem isBounded_classicalSeparatedProductQuotient
    (b : BoundaryCondition) (Φ : Curve (ℂ × ℂ))
    (hΦ : MemLp (extend Φ) 2 (volume.restrict (Ioc 0 1))) :
    Bornology.IsBounded (range (classicalSeparatedProductQuotient b Φ hΦ)) := by
  have hr : 0 < Real.pi/4 := by positivity
  obtain ⟨R,B,hb⟩ := exists_bound_classicalSeparated_div_characteristic_exterior
    b Φ (by simp) (by norm_num)
    (intervalPotentialCoefficients (intervalL2OfFunction (extend Φ) hΦ))
    (intervalPotentialCoefficients_mem _) hr le_rfl
  obtain ⟨R',hR'⟩ := b.exists_threshold_half_le_norm_characteristic_div_sin
    (by simp) (by norm_num)
    (intervalPotentialCoefficients (intervalL2OfFunction (extend Φ) hΦ))
    (intervalPotentialCoefficients_mem _) hr le_rfl
  apply isBounded_entire_of_bound_off_freeDiscs
    (fun z => (analyticOnNhd_classicalSeparatedProductQuotient b Φ hΦ z (mem_univ _)).differentiableAt)
    hr le_rfl (max R R') B
  intro z hz hsep
  have hg : b.characteristic (by simp)
        (intervalPotentialCoefficients (intervalL2OfFunction (extend Φ) hΦ))
        (intervalPotentialCoefficients_mem _) z ≠ 0 := by
    have hl := hR' z (le_trans (le_max_right R R') hz) hsep
    intro he
    simp only [he,zero_div,norm_zero] at hl
    norm_num at hl
  rw [classicalSeparatedProductQuotient,analyticQuotient_eq_div
    (analyticOnNhd_classicalSeparatedCharacteristic b Φ)
    (b.analyticOnNhd_characteristic (by simp) (by norm_num)
      _ (intervalPotentialCoefficients_mem _)) z hg]
  exact hb z (le_trans (le_max_left R R') hz) hsep

/-- The filled quotient tends to one on a fixed vertical sequence whose
imaginary height escapes to infinity. -/
theorem tendsto_classicalSeparatedProductQuotient_upper
    (b : BoundaryCondition) (Φ : Curve (ℂ × ℂ))
    (hΦ : MemLp (extend Φ) 2 (volume.restrict (Ioc 0 1))) :
    Tendsto (fun k : ℕ => classicalSeparatedProductQuotient b Φ hΦ
      (verticalSpectralPoint 0 ((k : ℝ)+Real.pi))) atTop (𝓝 1) := by
  let z : ℕ → ℂ := fun k => verticalSpectralPoint 0 ((k : ℝ)+Real.pi)
  have hy : Tendsto (fun k : ℕ => (k : ℝ)+Real.pi) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hz : Tendsto (fun k => (z k).im) atTop atTop := by
    simpa only [z,verticalSpectralPoint_im] using hy
  have hescape : Tendsto (fun k => ‖z k‖) atTop atTop := by
    apply tendsto_atTop_mono _ hy
    intro k
    have h := Complex.abs_im_le_norm (z k)
    have hpos : 0 ≤ (k : ℝ)+Real.pi := by positivity
    simpa only [z,verticalSpectralPoint_im,abs_of_nonneg hpos] using h
  have hr : 0 < Real.pi/4 := by positivity
  have hsep (k : ℕ) (n : ℤ) :
      Real.pi/4 ≤ ‖z k-(Real.pi : ℂ)*n‖ := by
    have h := Complex.abs_im_le_norm (z k-(Real.pi : ℂ)*n)
    have hpos : 0 ≤ (k : ℝ)+Real.pi := by positivity
    have hbound : Real.pi/4 ≤ (k : ℝ)+Real.pi := by
      have : 0 ≤ (k : ℝ) := by positivity
      have : 0 ≤ Real.pi := Real.pi_pos.le
      linarith
    have h' : (k : ℝ)+Real.pi ≤ ‖z k-(Real.pi : ℂ)*n‖ := by
      simpa [z,verticalSpectralPoint_im,abs_of_nonneg hpos] using h
    exact hbound.trans h'
  have hratio := tendsto_classicalSeparated_div_characteristic_upper_of_separated
    (by simp) (by norm_num) b Φ
    (intervalPotentialCoefficients (intervalL2OfFunction (extend Φ) hΦ))
    (intervalPotentialCoefficients_mem _) z hz hescape hr le_rfl hsep
  have he : (fun k => classicalSeparatedProductQuotient b Φ hΦ (z k)) =ᶠ[atTop]
      (fun k => classicalSeparatedCharacteristic b Φ (z k) /
        b.characteristic (by simp)
          (intervalPotentialCoefficients (intervalL2OfFunction (extend Φ) hΦ))
          (intervalPotentialCoefficients_mem _) (z k)) := by
    filter_upwards [hratio.eventually_ne one_ne_zero] with k hk
    have hg := (div_ne_zero_iff.mp hk).2
    exact analyticQuotient_eq_div
      (analyticOnNhd_classicalSeparatedCharacteristic b Φ)
      (b.analyticOnNhd_characteristic (by simp) (by norm_num)
        _ (intervalPotentialCoefficients_mem _)) (z k) hg
  simpa only [z] using hratio.congr' he.symm

/-- The source-normalized intrinsic boundary product is exactly the literal
classical separated monodromy characteristic for continuous physical data. -/
theorem characteristic_eq_classicalSeparated
    (b : BoundaryCondition) (Φ : Curve (ℂ × ℂ))
    (hΦ : MemLp (extend Φ) 2 (volume.restrict (Ioc 0 1))) (z : ℂ) :
    b.characteristic (by simp)
      (intervalPotentialCoefficients (intervalL2OfFunction (extend Φ) hΦ))
      (intervalPotentialCoefficients_mem _) z =
        classicalSeparatedCharacteristic b Φ z := by
  have ha := analyticOnNhd_classicalSeparatedProductQuotient b Φ hΦ
  have hc := eq_const_of_bounded_entire_of_tendsto_path
    (fun w => (ha w (mem_univ _)).differentiableAt)
    (isBounded_classicalSeparatedProductQuotient b Φ hΦ)
    (fun k : ℕ => verticalSpectralPoint 0 ((k : ℝ)+Real.pi)) 1
    (tendsto_classicalSeparatedProductQuotient_upper b Φ hΦ)
  simpa only [hc z,one_mul] using
    (classicalSeparatedProductQuotient_mul b Φ hΦ z)

end NLS.ZakharovShabat
