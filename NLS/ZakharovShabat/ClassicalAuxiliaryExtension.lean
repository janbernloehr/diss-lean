import NLS.ZakharovShabat.ClassicalAuxiliaryPhase
import NLS.ZakharovShabat.AuxiliarySpaces

/-!
# The physical auxiliary extension and its weighted domain

Conjugating the signed ordinary extension gives exactly the source reflection
(-i f₊, i f₋) on the second half, with the boundary sign. Its weighted Fourier
representative reconstructs the original auxiliary H¹ function, including both
endpoints. Extension and restriction identify precisely the auxiliary domain.
-/

noncomputable section
open MeasureTheory Set NLS.Fourier
namespace NLS.ZakharovShabat.BoundaryCondition

/-- The source physical auxiliary extension, as a linear map on actual functions. -/
def auxiliaryIntervalExtension (b : BoundaryCondition) : (ℝ → ℂ × ℂ) →ₗ[ℂ] (ℝ → ℂ × ℂ) :=
  physicalAuxiliaryPhase.toLinearMap.comp ((intervalExtension b).comp physicalAuxiliaryPhase.symm.toLinearMap)

theorem auxiliaryIntervalExtension_left (b : BoundaryCondition) (f : ℝ → ℂ × ℂ)
    (x : ℝ) (hx : x ≤ 1) : auxiliaryIntervalExtension b f x = f x := by
  change auxiliaryPhase ℂ (intervalExtension b (physicalAuxiliaryPhase.symm f) x) = f x
  rw [intervalExtension_left b _ x hx]
  exact (auxiliaryPhase ℂ).apply_symm_apply (f x)

/-- The reflected half has exactly the two source phase factors. -/
theorem auxiliaryIntervalExtension_right (b : BoundaryCondition) (f : ℝ → ℂ × ℂ)
    (x : ℝ) (hx : 1 < x) : auxiliaryIntervalExtension b f x =
      extensionSign b • (-Complex.I * (f (2-x)).2, Complex.I * (f (2-x)).1) := by
  change auxiliaryPhase ℂ (intervalExtension b (physicalAuxiliaryPhase.symm f) x) = _
  rw [intervalExtension_right b _ x hx]
  apply Prod.ext <;> simp [physicalAuxiliaryPhase_symm_apply, mul_left_comm]

/-- The actual Sobolev extension of an original auxiliary endpoint function. -/
def classicalAuxiliaryExtension (b : BoundaryCondition) (f : ℝ → ℂ × ℂ)
    (hf : HasClassicalAuxiliaryDomain b f) : Domain 2 :=
  auxiliaryPhase (ScalarDomain 2) (classicalIntervalExtension b (physicalAuxiliaryPhase.symm f)
    ((hasClassicalAuxiliaryDomain_iff b f).mp hf))

theorem classicalAuxiliaryExtension_mem (b : BoundaryCondition) (f : ℝ → ℂ × ℂ)
    (hf : HasClassicalAuxiliaryDomain b f) : classicalAuxiliaryExtension b f hf ∈ auxiliaryDomain b :=
  ⟨_, classicalIntervalExtension_mem b _ _, rfl⟩

/-- Sobolev synthesis commutes with the coefficient and physical phase rotations. -/
theorem classicalIntervalRestriction_auxiliaryPhase (a : Domain 2) :
    classicalIntervalRestriction (auxiliaryPhase (ScalarDomain 2) a) =
      physicalAuxiliaryPhase (classicalIntervalRestriction a) := by
  funext x
  apply Prod.ext
  · rfl
  · simp [classicalIntervalRestriction, map_smul]

theorem classicalIntervalRestriction_auxiliaryPhase_symm (a : Domain 2) :
    classicalIntervalRestriction ((auxiliaryPhase (ScalarDomain 2)).symm a) =
      physicalAuxiliaryPhase.symm (classicalIntervalRestriction a) := by
  apply physicalAuxiliaryPhase.injective
  rw [LinearEquiv.apply_symm_apply, ← classicalIntervalRestriction_auxiliaryPhase,
    LinearIsometryEquiv.apply_symm_apply]

/-- The Fourier extension reconstructs the actual source extension on the entire period. -/
theorem classicalAuxiliaryExtension_reconstruct (b : BoundaryCondition) (f : ℝ → ℂ × ℂ)
    (hf : HasClassicalAuxiliaryDomain b f) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 2) :
    classicalIntervalRestriction (classicalAuxiliaryExtension b f hf) x = auxiliaryIntervalExtension b f x := by
  rw [classicalAuxiliaryExtension, classicalIntervalRestriction_auxiliaryPhase]
  change auxiliaryPhase ℂ (classicalIntervalRestriction (classicalIntervalExtension b _ _) x) = _
  rw [show classicalIntervalRestriction (classicalIntervalExtension b (physicalAuxiliaryPhase.symm f) _) x =
    intervalExtension b (physicalAuxiliaryPhase.symm f) x from classicalIntervalExtension_reconstruct b _ _ hx]
  rfl

theorem classicalAuxiliaryExtension_restrict (b : BoundaryCondition) (f : ℝ → ℂ × ℂ)
    (hf : HasClassicalAuxiliaryDomain b f) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    classicalIntervalRestriction (classicalAuxiliaryExtension b f hf) x = f x := by
  rw [classicalAuxiliaryExtension_reconstruct b f hf ⟨hx.1, hx.2.trans (by norm_num)⟩,
    auxiliaryIntervalExtension_left b f x hx.2]

/-- Every auxiliary coefficient-domain vector satisfies the original physical endpoint equations. -/
theorem classicalIntervalRestriction_mem_auxiliary (b : BoundaryCondition) (a : Domain 2)
    (ha : a ∈ auxiliaryDomain b) : HasClassicalAuxiliaryDomain b (classicalIntervalRestriction a) := by
  apply (hasClassicalAuxiliaryDomain_iff b _).mpr
  rw [← classicalIntervalRestriction_auxiliaryPhase_symm]
  exact classicalIntervalRestriction_mem b _ ((mem_auxiliaryDomain b a).mp ha)

/-- Extending the physical restriction recovers every auxiliary coefficient vector. -/
@[simp] theorem classicalAuxiliaryExtension_classicalIntervalRestriction (b : BoundaryCondition)
    (a : Domain 2) (ha : a ∈ auxiliaryDomain b) :
    classicalAuxiliaryExtension b (classicalIntervalRestriction a)
      (classicalIntervalRestriction_mem_auxiliary b a ha) = a := by
  unfold classicalAuxiliaryExtension
  have he := classicalIntervalExtension_congr b
    (physicalAuxiliaryPhase.symm (classicalIntervalRestriction a))
    (classicalIntervalRestriction ((auxiliaryPhase (ScalarDomain 2)).symm a))
    ((hasClassicalAuxiliaryDomain_iff b _).mp (classicalIntervalRestriction_mem_auxiliary b a ha))
    (classicalIntervalRestriction_mem b _ ((mem_auxiliaryDomain b a).mp ha))
    (fun x _ => congrFun (classicalIntervalRestriction_auxiliaryPhase_symm a).symm x)
  rw [he, classicalIntervalExtension_classicalIntervalRestriction b _ ((mem_auxiliaryDomain b a).mp ha)]
  exact (auxiliaryPhase (ScalarDomain 2)).apply_symm_apply a

/-- The coefficient auxiliary domain is exactly the extensions of original auxiliary H¹ functions. -/
theorem mem_auxiliaryDomain_iff_exists_classicalAuxiliaryExtension (b : BoundaryCondition) (a : Domain 2) :
    a ∈ auxiliaryDomain b ↔ ∃ (f : ℝ → ℂ × ℂ) (hf : HasClassicalAuxiliaryDomain b f),
      classicalAuxiliaryExtension b f hf = a := by
  constructor
  · intro ha
    exact ⟨classicalIntervalRestriction a, classicalIntervalRestriction_mem_auxiliary b a ha,
      classicalAuxiliaryExtension_classicalIntervalRestriction b a ha⟩
  · rintro ⟨f, hf, rfl⟩
    exact classicalAuxiliaryExtension_mem b f hf

/-- Only original interval values affect the auxiliary extension. -/
theorem classicalAuxiliaryExtension_congr (b : BoundaryCondition) (f g : ℝ → ℂ × ℂ)
    (hf : HasClassicalAuxiliaryDomain b f) (hg : HasClassicalAuxiliaryDomain b g)
    (h : EqOn f g (Icc 0 1)) : classicalAuxiliaryExtension b f hf = classicalAuxiliaryExtension b g hg := by
  unfold classicalAuxiliaryExtension
  congr 1
  apply classicalIntervalExtension_congr
  intro x hx
  exact congrArg (auxiliaryPhase ℂ).symm (h hx)

/-- Auxiliary weighted representatives are determined by their restriction to the original interval. -/
theorem classicalIntervalRestriction_injective_on_auxiliaryDomain (b : BoundaryCondition)
    (a c : Domain 2) (ha : a ∈ auxiliaryDomain b) (hc : c ∈ auxiliaryDomain b)
    (h : EqOn (classicalIntervalRestriction a) (classicalIntervalRestriction c) (Icc 0 1)) : a = c := by
  have he := classicalAuxiliaryExtension_congr b _ _
    (classicalIntervalRestriction_mem_auxiliary b a ha) (classicalIntervalRestriction_mem_auxiliary b c hc) h
  rw [classicalAuxiliaryExtension_classicalIntervalRestriction b a ha,
    classicalAuxiliaryExtension_classicalIntervalRestriction b c hc] at he
  exact he

/-- The original auxiliary endpoint function has a unique auxiliary weighted representative. -/
theorem existsUnique_classicalAuxiliaryRepresentative (b : BoundaryCondition)
    (f : ℝ → ℂ × ℂ) (hf : HasClassicalAuxiliaryDomain b f) :
    ∃! a : Domain 2, a ∈ auxiliaryDomain b ∧ EqOn (classicalIntervalRestriction a) f (Icc 0 1) := by
  refine ⟨classicalAuxiliaryExtension b f hf, ⟨classicalAuxiliaryExtension_mem b f hf, ?_⟩, ?_⟩
  · intro x hx
    exact classicalAuxiliaryExtension_restrict b f hf hx
  · intro a ha
    apply classicalIntervalRestriction_injective_on_auxiliaryDomain b a _ ha.1 (classicalAuxiliaryExtension_mem b f hf)
    intro x hx
    exact (ha.2 hx).trans (classicalAuxiliaryExtension_restrict b f hf hx).symm

end NLS.ZakharovShabat.BoundaryCondition
