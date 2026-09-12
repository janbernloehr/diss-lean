import NLS.ZakharovShabat.ClassicalIntervalNorm

/-!
# Original interval functions as linear boundary domains

Elements are actual functions on the closed interval `[0,1]`, so equality does
not depend on arbitrary values outside it. Membership is characterized by the
original classical `H¹` and endpoint conditions. The Fourier restriction range
provides the pointwise linear structure and the algebraic extension inverse.
The physical norm and continuity are constructed in `ClassicalIntervalIsomorphism`.
-/

noncomputable section
open Set NLS.Fourier
namespace NLS.ZakharovShabat.BoundaryCondition

/-- Physical restriction as a linear map into functions on the actual closed interval. -/
def intervalRestrictionLinear (b : BoundaryCondition) :
    ↥(domain (p := 2) b) →ₗ[ℂ] (Icc (0 : ℝ) 1 → ℂ × ℂ) where
  toFun a x := classicalIntervalRestriction a.val x.val
  map_add' a c := by
    funext x
    simp [classicalIntervalRestriction]
  map_smul' c a := by
    funext x
    simp [classicalIntervalRestriction]

theorem intervalRestrictionLinear_injective (b : BoundaryCondition) :
    Function.Injective (intervalRestrictionLinear b) := by
  intro a c h
  apply Subtype.ext
  apply classicalIntervalRestriction_injective_on_domain b a.val c.val a.property c.property
  intro x hx
  exact congrFun h ⟨x, hx⟩

/-- The linear subspace of classical endpoint-domain functions on the original interval. -/
def classicalIntervalSubmodule (b : BoundaryCondition) :
    Submodule ℂ (Icc (0 : ℝ) 1 → ℂ × ℂ) := (intervalRestrictionLinear b).range

/-- This range is exactly the original classical domain, without a periodicity assumption. -/
theorem mem_classicalIntervalSubmodule_iff (b : BoundaryCondition) (u : Icc (0 : ℝ) 1 → ℂ × ℂ) :
    u ∈ classicalIntervalSubmodule b ↔ ∃ f : ℝ → ℂ × ℂ,
      HasClassicalIntervalDomain b f ∧ ∀ x : Icc (0 : ℝ) 1, u x = f x.val := by
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨classicalIntervalRestriction a.val,
      classicalIntervalRestriction_mem b a.val a.property, fun _ => rfl⟩
  · rintro ⟨f, hf, hu⟩
    refine ⟨⟨classicalIntervalExtension b f hf, classicalIntervalExtension_mem b f hf⟩, ?_⟩
    funext x
    exact (classicalIntervalExtension_restrict b f hf x.property).trans (hu x).symm

/-- Classical Dirichlet or Neumann functions on `[0,1]`, with pointwise vector operations. -/
def ClassicalIntervalDomain (b : BoundaryCondition) := ↥(classicalIntervalSubmodule b)

instance (b : BoundaryCondition) : AddCommGroup (ClassicalIntervalDomain b) :=
  inferInstanceAs (AddCommGroup ↥(classicalIntervalSubmodule b))

instance (b : BoundaryCondition) : Module ℂ (ClassicalIntervalDomain b) :=
  inferInstanceAs (Module ℂ ↥(classicalIntervalSubmodule b))

/-- The algebraic restriction equivalence; its inverse is the signed interval extension. -/
def classicalRestrictionLinearEquiv (b : BoundaryCondition) :
    ↥(domain (p := 2) b) ≃ₗ[ℂ] ClassicalIntervalDomain b :=
  LinearEquiv.ofInjective (intervalRestrictionLinear b) (intervalRestrictionLinear_injective b)

@[simp] theorem classicalRestrictionLinearEquiv_apply (b : BoundaryCondition)
    (a : ↥(domain (p := 2) b)) (x : Icc (0 : ℝ) 1) :
    (classicalRestrictionLinearEquiv b a).val x = classicalIntervalRestriction a.val x.val := rfl

/-- An arbitrary original classical pair defines an element of the actual interval space. -/
def classicalDomainOfFunction (b : BoundaryCondition) (f : ℝ → ℂ × ℂ)
    (hf : HasClassicalIntervalDomain b f) : ClassicalIntervalDomain b :=
  ⟨fun x => f x.val, (mem_classicalIntervalSubmodule_iff b _).mpr ⟨f, hf, fun _ => rfl⟩⟩

@[simp] theorem classicalDomainOfFunction_apply (b : BoundaryCondition) (f : ℝ → ℂ × ℂ)
    (hf : HasClassicalIntervalDomain b f) (x : Icc (0 : ℝ) 1) :
    (classicalDomainOfFunction b f hf).val x = f x.val := rfl

/-- The inverse algebraic map is exactly the previously constructed physical Fourier extension. -/
@[simp] theorem classicalRestrictionLinearEquiv_symm_ofFunction (b : BoundaryCondition)
    (f : ℝ → ℂ × ℂ) (hf : HasClassicalIntervalDomain b f) :
    (classicalRestrictionLinearEquiv b).symm (classicalDomainOfFunction b f hf) =
      ⟨classicalIntervalExtension b f hf, classicalIntervalExtension_mem b f hf⟩ := by
  apply (classicalRestrictionLinearEquiv b).injective
  rw [LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  funext x
  exact (classicalIntervalExtension_restrict b f hf x.property).symm

/-- A canonical real-line representative of an interval-domain element. -/
def classicalDomainRepresentative (b : BoundaryCondition) (u : ClassicalIntervalDomain b) :
    ℝ → ℂ × ℂ := classicalIntervalRestriction ((classicalRestrictionLinearEquiv b).symm u).val

theorem classicalDomainRepresentative_mem (b : BoundaryCondition) (u : ClassicalIntervalDomain b) :
    HasClassicalIntervalDomain b (classicalDomainRepresentative b u) :=
  classicalIntervalRestriction_mem b _ ((classicalRestrictionLinearEquiv b).symm u).property

/-- The canonical representative has exactly the stored interval values. -/
theorem classicalDomainRepresentative_apply (b : BoundaryCondition) (u : ClassicalIntervalDomain b)
    (x : Icc (0 : ℝ) 1) : classicalDomainRepresentative b u x.val = u.val x := by
  exact congrArg (fun v : ClassicalIntervalDomain b => v.val x)
    ((classicalRestrictionLinearEquiv b).apply_symm_apply u)

/-- Passing through a real-line representative does not change the interval-domain element. -/
@[simp] theorem classicalDomainOfFunction_representative (b : BoundaryCondition)
    (u : ClassicalIntervalDomain b) :
    classicalDomainOfFunction b (classicalDomainRepresentative b u)
      (classicalDomainRepresentative_mem b u) = u := by
  apply Subtype.ext
  funext x
  exact classicalDomainRepresentative_apply b u x

/-- Every element is represented by original classical endpoint-domain data. -/
theorem classicalDomainOfFunction_surjective (b : BoundaryCondition) (u : ClassicalIntervalDomain b) :
    ∃ (f : ℝ → ℂ × ℂ) (hf : HasClassicalIntervalDomain b f), classicalDomainOfFunction b f hf = u :=
  ⟨classicalDomainRepresentative b u, classicalDomainRepresentative_mem b u,
    classicalDomainOfFunction_representative b u⟩

/-- Elements are continuous functions on the original closed interval. -/
theorem continuous_classicalIntervalDomain (b : BoundaryCondition) (u : ClassicalIntervalDomain b) :
    Continuous u.val := by
  let a := (classicalRestrictionLinearEquiv b).symm u
  have h := ((continuous_sobolevSynthesis (by simp) a.val.1).prodMk
    (continuous_sobolevSynthesis (by simp) a.val.2)).comp
    (continuous_subtype_val : Continuous (fun x : Icc (0 : ℝ) 1 => x.val))
  convert h using 1
  funext x
  exact (classicalDomainRepresentative_apply b u x).symm

/-- The left endpoint satisfies the source's equal or opposite component condition. -/
theorem classicalIntervalDomain_left (b : BoundaryCondition) (u : ClassicalIntervalDomain b) :
    (u.val ⟨0, by norm_num⟩).1 = extensionSign b * (u.val ⟨0, by norm_num⟩).2 := by
  have h := (classicalDomainRepresentative_mem b u).left
  rw [classicalDomainRepresentative_apply b u ⟨0, by norm_num⟩] at h
  exact h

/-- The right endpoint has the same boundary sign; no period-one endpoint equality is imposed. -/
theorem classicalIntervalDomain_right (b : BoundaryCondition) (u : ClassicalIntervalDomain b) :
    (u.val ⟨1, by norm_num⟩).1 = extensionSign b * (u.val ⟨1, by norm_num⟩).2 := by
  have h := (classicalDomainRepresentative_mem b u).right
  rw [classicalDomainRepresentative_apply b u ⟨1, by norm_num⟩] at h
  exact h

end NLS.ZakharovShabat.BoundaryCondition
