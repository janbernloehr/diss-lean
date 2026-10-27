import NLS.ZakharovShabat.AKNSIntervalOperator
import NLS.ZakharovShabat.ClassicalAuxiliaryReality

/-! # Real AKNS potential coordinates for the original physical L2 potentials -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set
open scoped ComplexConjugate
namespace NLS.ZakharovShabat

/-- Inverse potential coordinates, without the unitary vector normalization. -/
def aknsPotentialInverse (φ : ℂ × ℂ) : ℂ × ℂ :=
  ((φ.1+φ.2)/2,(φ.1-φ.2)/(2*Complex.I))

@[simp] theorem aknsPotentialInverse_potential (q p : ℂ) :
    aknsPotentialInverse (aknsPotential q p) = (q,p) := by
  ext <;> dsimp [aknsPotentialInverse,aknsPotential] <;> field_simp <;> ring

@[simp] theorem aknsPotential_inverse (φ : ℂ × ℂ) :
    aknsPotential (aknsPotentialInverse φ).1 (aknsPotentialInverse φ).2 = φ := by
  ext <;> dsimp [aknsPotentialInverse,aknsPotential] <;> field_simp <;> ring

/-- Physical real type is exactly reality of both unnormalized AKNS coordinates. -/
theorem aknsPotential_realType_iff (q p : ℂ) :
    (aknsPotential q p).2 = conj (aknsPotential q p).1 ↔ q.im = 0 ∧ p.im = 0 := by
  constructor
  · intro h
    have hr := congrArg Complex.re h
    have hi := congrArg Complex.im h
    simp [aknsPotential] at hr hi
    constructor <;> linarith
  · rintro ⟨hq,hp⟩
    apply Complex.ext <;> simp [aknsPotential,hq,hp]

/-- The inverse coordinates of a conjugate pair are real, with no regularity hypothesis. -/
theorem aknsPotentialInverse_real_iff (φ : ℂ × ℂ) :
    (aknsPotentialInverse φ).1.im = 0 ∧ (aknsPotentialInverse φ).2.im = 0 ↔
      φ.2 = conj φ.1 := by
  simpa only [aknsPotential_inverse] using
    (aknsPotential_realType_iff (aknsPotentialInverse φ).1 (aknsPotentialInverse φ).2).symm

/-- The original almost-everywhere real-type condition permits arbitrary representatives. -/
theorem isClassicalRealType_aknsPotential_iff (q p : ℝ → ℂ) :
    IsClassicalRealType (fun x => aknsPotential (q x) (p x)) ↔
      ∀ᵐ x ∂volume.restrict (Ioc 0 1), (q x).im = 0 ∧ (p x).im = 0 := by
  change (∀ᵐ x ∂volume.restrict (Ioc 0 1),
    (aknsPotential (q x) (p x)).2 = conj (aknsPotential (q x) (p x)).1) ↔ _
  exact Filter.eventually_congr (Filter.Eventually.of_forall (fun x => aknsPotential_realType_iff (q x) (p x)))

/-- Inverse potential coordinates preserve the original physical L2 class. -/
theorem memLp_aknsPotentialInverse {φ : ℝ → ℂ × ℂ}
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) :
    MemLp (fun x => (aknsPotentialInverse (φ x)).1) 2 (volume.restrict (Ioc 0 1)) ∧
    MemLp (fun x => (aknsPotentialInverse (φ x)).2) 2 (volume.restrict (Ioc 0 1)) := by
  obtain ⟨h1,h2⟩ := memLp_prod_iff.mp hφ
  simpa only [aknsPotentialInverse,div_eq_mul_inv,Pi.add_apply,Pi.sub_apply] using
    And.intro ((h1.add h2).mul_const (2 : ℂ)⁻¹)
      ((h1.sub h2).mul_const (2*Complex.I)⁻¹)

/-- Every original real-type physical L2 potential has real AKNS coordinates
in L2, with exact reconstruction almost everywhere. -/
theorem exists_real_aknsPotential_coordinates {φ : ℝ → ℂ × ℂ}
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) (hr : IsClassicalRealType φ) :
    ∃ q p : ℝ → ℝ,
      MemLp (fun x => (q x : ℂ)) 2 (volume.restrict (Ioc 0 1)) ∧
      MemLp (fun x => (p x : ℂ)) 2 (volume.restrict (Ioc 0 1)) ∧
      φ =ᵐ[volume.restrict (Ioc 0 1)] (fun x => aknsPotential (q x) (p x)) := by
  have hre : ∀ᵐ x ∂volume.restrict (Ioc 0 1),
      (((aknsPotentialInverse (φ x)).1.re : ℝ) : ℂ) = (aknsPotentialInverse (φ x)).1 ∧
      (((aknsPotentialInverse (φ x)).2.re : ℝ) : ℂ) = (aknsPotentialInverse (φ x)).2 := by
    filter_upwards [hr] with x hx
    have hh := (aknsPotentialInverse_real_iff (φ x)).mpr hx
    constructor <;> apply Complex.ext <;> simp [hh.1,hh.2]
  obtain ⟨h1,h2⟩ := memLp_aknsPotentialInverse hφ
  refine ⟨fun x => (aknsPotentialInverse (φ x)).1.re,
    fun x => (aknsPotentialInverse (φ x)).2.re,
    (memLp_congr_ae (hre.mono (fun _ h => h.1))).mpr h1,
    (memLp_congr_ae (hre.mono (fun _ h => h.2))).mpr h2,?_⟩
  filter_upwards [hre] with x hx
  rw [hx.1,hx.2,aknsPotential_inverse]

end NLS.ZakharovShabat
