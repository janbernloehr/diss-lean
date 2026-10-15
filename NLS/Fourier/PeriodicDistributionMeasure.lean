import NLS.Fourier.ComplexMeasureRepresentation
/-! # Appendix A: order-zero distributions and complex Radon measures

Every original distribution of least order zero is integration against a
unique finite complex Radon measure. The normalized action retains 1/L on
the physical circle, including complex point masses. Conversely, every complex
Borel measure gives an order-zero distribution. This proves (A.2).
-/
noncomputable section
open Set MeasureTheory
namespace NLS.Fourier
namespace SmoothPeriodicTest.Distribution
variable {L : ℝ} [Fact (0 < L)]

def ofComplexMeasure (μ : ComplexMeasure (AddCircle L)) : Distribution L :=
  ((L:ℂ)⁻¹ • complexMeasureContinuousIntegral μ).comp toContinuousCLM

theorem ofComplexMeasure_order (μ : ComplexMeasure (AddCircle L)) :
    (ofComplexMeasure μ).order = 0 := by
  apply (order_zero_iff_physical_extension _).mpr
  refine ⟨(L:ℂ)⁻¹ • complexMeasureContinuousIntegral μ,fun _ => rfl,?_⟩
  intro v hv
  apply DFunLike.coe_injective
  exact (denseRange_toContinuousCLM (L := L)).equalizer v.continuous
    ((L:ℂ)⁻¹ • complexMeasureContinuousIntegral μ).continuous (funext hv)

theorem ofComplexMeasure_injective : Function.Injective (ofComplexMeasure (L := L)) := by
  intro μ ν h
  have he : (L:ℂ)⁻¹ • complexMeasureContinuousIntegral μ =
      (L:ℂ)⁻¹ • complexMeasureContinuousIntegral ν := by
    apply DFunLike.coe_injective
    apply (denseRange_toContinuousCLM (L := L)).equalizer
      ((L:ℂ)⁻¹ • complexMeasureContinuousIntegral μ).continuous
      ((L:ℂ)⁻¹ • complexMeasureContinuousIntegral ν).continuous
    funext f
    exact congrArg (fun u : Distribution L => u f) h
  apply complexMeasureContinuousIntegral_injective
  ext f
  have hf := congrArg (fun F : C(AddCircle L,ℂ) →L[ℂ] ℂ => F f) he
  exact mul_left_cancel₀ (inv_ne_zero (Complex.ofReal_ne_zero.mpr (Fact.out : 0 < L).ne')) hf

theorem order_zero_iff_measure (u : Distribution L) :
    u.order = 0 ↔ ∃! μ : ComplexMeasure (AddCircle L), ofComplexMeasure μ = u := by
  constructor
  · intro hu
    obtain ⟨F,hF,_⟩ := (order_zero_iff_physical_extension u).mp hu
    obtain ⟨μ,hμ⟩ := complexMeasureContinuousIntegral_surjective ((L:ℂ) • F)
    have he : ofComplexMeasure μ = u := by
      ext f
      change (L:ℂ)⁻¹ * complexMeasureContinuousIntegral μ (toContinuousCLM f) = u f
      rw [hμ]
      change (L:ℂ)⁻¹ * ((L:ℂ) * F (toContinuousCLM f)) = u f
      rw [inv_mul_cancel_left₀ (Complex.ofReal_ne_zero.mpr (Fact.out : 0 < L).ne'),hF]
    exact ⟨μ,he,fun ν hν => ofComplexMeasure_injective (hν.trans he.symm)⟩
  · rintro ⟨μ,rfl,_⟩
    exact ofComplexMeasure_order μ

theorem ofComplexMeasure_apply (μ : ComplexMeasure (AddCircle L)) (f : SmoothPeriodicTest L) :
    ofComplexMeasure μ f = (L:ℂ)⁻¹ * complexMeasureContinuousIntegral μ (toContinuousCLM f) := rfl

theorem ofComplexMeasure_zero_coefficient (μ : ComplexMeasure (AddCircle L)) :
    ofComplexMeasure μ (mode 0) = (L:ℂ)⁻¹ * μ univ := by
  rw [ofComplexMeasure_apply]
  have he : toContinuousCLM (mode 0 : SmoothPeriodicTest L) = ContinuousMap.const (AddCircle L) 1 := by
    ext y
    obtain ⟨x,rfl⟩ := QuotientAddGroup.mk_surjective y
    rw [toContinuousCLM_apply,mode_apply_physical]
    simp
  rw [he,complexMeasureContinuousIntegral_const,one_mul]

theorem ofComplexMeasure_dirac (x : ℝ) (z : ℂ) :
    ofComplexMeasure (VectorMeasure.dirac (x : AddCircle L) ((L:ℂ)*z)) = z • evaluation x := by
  ext f
  rw [ofComplexMeasure_apply,complexMeasureContinuousIntegral_dirac,toContinuousCLM_apply]
  change (L:ℂ)⁻¹ * ((L:ℂ)*z*f x) = z*f x
  field_simp [Complex.ofReal_ne_zero.mpr (Fact.out : 0 < L).ne']

theorem existsUnique_normalized_measure (F : C(AddCircle L,ℂ) →L[ℂ] ℂ) :
    ∃! μ : ComplexMeasure (AddCircle L), ∀ f : C(AddCircle L,ℂ),
      F f = (L:ℂ)⁻¹ * complexMeasureContinuousIntegral μ f := by
  obtain ⟨μ,hμ⟩ := complexMeasureContinuousIntegral_surjective ((L:ℂ) • F)
  have hL : (L:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Fact.out : 0 < L).ne'
  have he (f : C(AddCircle L,ℂ)) : F f = (L:ℂ)⁻¹ * complexMeasureContinuousIntegral μ f := by
    rw [hμ]
    change F f = (L:ℂ)⁻¹ * ((L:ℂ)*F f)
    rw [inv_mul_cancel_left₀ hL]
  refine ⟨μ,he,fun ν hν => ?_⟩
  apply complexMeasureContinuousIntegral_injective
  ext f
  exact mul_left_cancel₀ (inv_ne_zero hL) ((hν f).symm.trans (he f))

def complexMeasureOrderZeroEquiv : ComplexMeasure (AddCircle L) ≃ {u : Distribution L // u.order = 0} :=
  Equiv.ofBijective (fun μ => ⟨ofComplexMeasure μ,ofComplexMeasure_order μ⟩)
    ⟨fun _ _ h => ofComplexMeasure_injective (congrArg Subtype.val h),by
      rintro ⟨u,hu⟩
      obtain ⟨μ,hμ,_⟩ := (order_zero_iff_measure u).mp hu
      exact ⟨μ,Subtype.ext hμ⟩⟩

end SmoothPeriodicTest.Distribution
end NLS.Fourier
