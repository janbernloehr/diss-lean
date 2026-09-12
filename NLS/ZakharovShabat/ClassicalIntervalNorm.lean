import NLS.Fourier.FoldedEnergy
import NLS.ZakharovShabat.ClassicalIntervalRestriction

/-!
# Physical norms for the classical boundary-domain correspondence

The original pair norm uses the sum of the two component `H¹` energies on
`[0,1]`. The Fourier pair uses the repository's maximum weighted norm. Reflection
makes the two weighted component norms equal, giving explicit comparison in
both directions. This supplies the norm estimates for Lemma 4.2.
-/

noncomputable section
open MeasureTheory Set NLS.Fourier
namespace NLS.ZakharovShabat.BoundaryCondition

/-- The standard component-sum classical Sobolev energy on the original interval. -/
def classicalIntervalEnergy (f : ℝ → ℂ × ℂ) : ℝ :=
  intervalH1Energy (fun x => (f x).1) 0 1 + intervalH1Energy (fun x => (f x).2) 0 1

/-- The physical pair `H¹` norm, before quotienting functions by equality on `[0,1]`. -/
def classicalIntervalNorm (f : ℝ → ℂ × ℂ) : ℝ := Real.sqrt (classicalIntervalEnergy f)

theorem classicalIntervalEnergy_nonneg (f : ℝ → ℂ × ℂ) : 0 ≤ classicalIntervalEnergy f :=
  add_nonneg (intervalH1Energy_nonneg _ (by norm_num)) (intervalH1Energy_nonneg _ (by norm_num))

/-- Energy is independent of the values chosen outside the original interval. -/
theorem classicalIntervalEnergy_congr {f g : ℝ → ℂ × ℂ} (hfg : EqOn f g (Icc 0 1)) :
    classicalIntervalEnergy f = classicalIntervalEnergy g := by
  unfold classicalIntervalEnergy
  rw [intervalH1Energy_congr (by norm_num) (fun x hx => congrArg Prod.fst (hfg hx)),
    intervalH1Energy_congr (by norm_num) (fun x hx => congrArg Prod.snd (hfg hx))]

/-- On a boundary reflection graph the pair norm equals either component norm. -/
theorem norm_eq_fst_of_mem_domain (b : BoundaryCondition) (a : Domain 2) (ha : a ∈ domain b) :
    ‖a‖ = ‖a.1‖ := by
  have he : ‖a.1‖ = ‖a.2‖ := by
    rw [(mem_domain_iff_reflection b a).mp ha, norm_smul, (WeightedCoeff.reflection 1).norm_map]
    cases b <;> simp [extensionSign]
  rw [Prod.norm_def, ← he, max_self]

/-- The first extended component has exactly the total original pair energy. -/
theorem classicalIntervalExtension_energy (b : BoundaryCondition) (f : ℝ → ℂ × ℂ)
    (hf : HasClassicalIntervalDomain b f) :
    intervalH1Energy (fun x : ℝ => sobolevSynthesis (by simp)
      (classicalIntervalExtension b f hf).1 (x : AddCircle (2 : ℝ))) 0 2 =
      classicalIntervalEnergy f := by
  calc
    _ = intervalH1Energy (fun x => (intervalExtension b f x).1) 0 2 :=
      intervalH1Energy_congr (by norm_num)
        (fun x hx => congrArg Prod.fst (classicalIntervalExtension_reconstruct b f hf hx))
    _ = _ := intervalH1Energy_folded (extensionSign b) (by cases b <;> simp [extensionSign])
      hf.fst_regular hf.snd_regular hf.right

/-- Two-sided energy bounds between the original physical domain and its weighted extension. -/
theorem classicalIntervalExtension_energy_bounds (b : BoundaryCondition) (f : ℝ → ℂ × ℂ)
    (hf : HasClassicalIntervalDomain b f) :
    ‖classicalIntervalExtension b f hf‖ ^ 2 ≤ classicalIntervalEnergy f ∧
    classicalIntervalEnergy f ≤ 2 * Real.pi ^ 2 * ‖classicalIntervalExtension b f hf‖ ^ 2 := by
  rw [norm_eq_fst_of_mem_domain b _ (classicalIntervalExtension_mem b f hf)]
  have h := intervalH1Energy_sobolevSynthesis_bounds (classicalIntervalExtension b f hf).1
  rw [classicalIntervalExtension_energy b f hf] at h
  exact h

/-- Extension is bounded by the physical norm, and restriction has bound `√2 π`. -/
theorem classicalIntervalExtension_norm_bounds (b : BoundaryCondition) (f : ℝ → ℂ × ℂ)
    (hf : HasClassicalIntervalDomain b f) :
    ‖classicalIntervalExtension b f hf‖ ≤ classicalIntervalNorm f ∧
    classicalIntervalNorm f ≤ Real.sqrt 2 * Real.pi * ‖classicalIntervalExtension b f hf‖ := by
  have he := classicalIntervalExtension_energy_bounds b f hf
  have hs := Real.sq_sqrt (classicalIntervalEnergy_nonneg f)
  have hs2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hn := Real.sqrt_nonneg (classicalIntervalEnergy f)
  have hc : 0 ≤ Real.sqrt 2 * Real.pi * ‖classicalIntervalExtension b f hf‖ := by positivity
  unfold classicalIntervalNorm
  constructor
  · nlinarith [norm_nonneg (classicalIntervalExtension b f hf)]
  · nlinarith [sq_nonneg (Real.sqrt 2 * Real.pi * ‖classicalIntervalExtension b f hf‖ -
      Real.sqrt (classicalIntervalEnergy f))]

/-- The same bounds apply directly to every weighted boundary pair under physical restriction. -/
theorem classicalIntervalRestriction_norm_bounds (b : BoundaryCondition) (a : Domain 2)
    (ha : a ∈ domain b) :
    ‖a‖ ≤ classicalIntervalNorm (classicalIntervalRestriction a) ∧
    classicalIntervalNorm (classicalIntervalRestriction a) ≤ Real.sqrt 2 * Real.pi * ‖a‖ := by
  have h := classicalIntervalExtension_norm_bounds b (classicalIntervalRestriction a)
    (classicalIntervalRestriction_mem b a ha)
  rw [classicalIntervalExtension_classicalIntervalRestriction b a ha] at h
  exact h

/-- Zero physical norm identifies the zero function on the original closed interval. -/
theorem classicalIntervalNorm_eq_zero_iff (b : BoundaryCondition) (f : ℝ → ℂ × ℂ)
    (hf : HasClassicalIntervalDomain b f) :
    classicalIntervalNorm f = 0 ↔ EqOn f 0 (Icc 0 1) := by
  constructor
  · intro h
    have hn := (classicalIntervalExtension_norm_bounds b f hf).1
    rw [h] at hn
    have he : classicalIntervalExtension b f hf = 0 := norm_eq_zero.mp (le_antisymm hn (norm_nonneg _))
    intro x hx
    have hr := classicalIntervalExtension_restrict b f hf hx
    rw [he] at hr
    change f x = (0, 0)
    simpa using hr.symm
  · intro h
    unfold classicalIntervalNorm
    rw [classicalIntervalEnergy_congr h]
    simp [classicalIntervalEnergy, intervalH1Energy]

end NLS.ZakharovShabat.BoundaryCondition
