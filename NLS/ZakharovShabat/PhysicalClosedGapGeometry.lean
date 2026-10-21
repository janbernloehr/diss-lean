import NLS.ZakharovShabat.PhysicalBirkhoffIntrinsicProperties
import Mathlib.LinearAlgebra.Isomorphisms

noncomputable section
open Set MeasureTheory Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Read both real Birkhoff coordinates of one physical spectral gap. -/
def physicalGapEvaluation (n : ℤ) : PhysicalRealBirkhoffTarget →L[ℝ] ℝ × ℝ :=
  ((lp.evalCLM ℝ (fun _ : ℤ => ℝ) 2 n).prodMap
    (lp.evalCLM ℝ (fun _ : ℤ => ℝ) 2 n)).comp
    physicalRealTargetEquiv.toContinuousLinearMap

/-- Insert an arbitrary real coordinate pair at the selected spectral index. -/
def physicalGapInsertion (n : ℤ) : (ℝ × ℝ) →L[ℝ] PhysicalRealBirkhoffTarget :=
  physicalRealTargetEquiv.symm.toContinuousLinearMap.comp
    ((lp.singleContinuousLinearMap ℝ (fun _ : ℤ => ℝ) 2 n).prodMap
      (lp.singleContinuousLinearMap ℝ (fun _ : ℤ => ℝ) 2 n))

@[simp] theorem physicalGapEvaluation_insertion (n : ℤ) (a : ℝ × ℝ) :
    physicalGapEvaluation n (physicalGapInsertion n a) = a := by
  apply Prod.ext
  · change (lp.single 2 n a.1 : RealCoeff 2) n = a.1
    simp
  · change (lp.single 2 n a.2 : RealCoeff 2) n = a.2
    simp

/-- Both real normal directions are attained by the bounded coordinate evaluation. -/
theorem physicalGapEvaluation_surjective (n : ℤ) :
    Function.Surjective (physicalGapEvaluation n) := fun a =>
  ⟨physicalGapInsertion n a,physicalGapEvaluation_insertion n a⟩

/-- The closed coordinate plane has exactly two real normal dimensions. -/
theorem physicalGapEvaluation_quotient_finrank (n : ℤ) :
    Module.finrank ℝ (PhysicalRealBirkhoffTarget ⧸ (physicalGapEvaluation n).ker) = 2 := by
  have he := ((physicalGapEvaluation n).toLinearMap.quotKerEquivOfSurjective
    (physicalGapEvaluation_surjective n)).finrank_eq
  simpa using he

/-- Literal real coordinates of the intrinsic physical map at one spectral index. -/
def physicalGapCoordinates (n : ℤ) (u : physicalRealSubmodule) : ℝ × ℝ :=
  physicalGapEvaluation n (intrinsicPhysicalBirkhoffMap u)

/-- The squared real coordinate radius is twice the original physical action. -/
theorem physicalGapCoordinates_radius (n : ℤ) (u : physicalRealSubmodule) :
    (physicalGapCoordinates n u).1^2 + (physicalGapCoordinates n u).2^2 =
      2*(physicalIndexedAction n u.val).re := by
  have hn := (physicalIndexedAction_nonneg u n).1
  change (Real.sqrt (2*(intrinsicPhysicalAction n u).re)*Real.cos (physicalTheta n u).re)^2+
    (Real.sqrt (2*(intrinsicPhysicalAction n u).re)*Real.sin (physicalTheta n u).re)^2 = _
  rw [intrinsicPhysicalAction_eq_indexed,mul_pow,mul_pow,
    Real.sq_sqrt (by positivity : 0 ≤ 2*(physicalIndexedAction n u.val).re)]
  calc
    _ = (2*(physicalIndexedAction n u.val).re)*
        (Real.sin (physicalTheta n u).re^2+Real.cos (physicalTheta n u).re^2) := by ring
    _ = _ := by rw [Real.sin_sq_add_cos_sq,mul_one]

/-- The original physical action vanishes exactly at gap collapse. -/
theorem physicalIndexedAction_zero_iff_closed (n : ℤ) (u : physicalRealSubmodule) :
    physicalIndexedAction n u.val = 0 ↔ physicalPeriodicLeft u.val n = physicalPeriodicRight u.val n := by
  have h := (sourceIndexedAction_nonneg_and_eq_zero_iff_gap_zero (by simp) (by norm_num)
    n (sourcePhysicalL2Equiv.symm u.val) u.property).2.2
  change physicalIndexedAction n u.val = 0 ↔ _ at h
  have hg : physicalPeriodicLeft u.val n = physicalPeriodicRight u.val n ↔
      sourcePeriodicGapDisplacement (by simp) (by norm_num) (sourcePhysicalL2Equiv.symm u.val) n = 0 := by
    simpa only [not_not] using (not_congr (physicalPeriodicGap_ne_iff u.val n))
  exact h.trans hg.symm

/-- A gap collapses precisely when both real coordinates vanish. -/
theorem physicalGapCoordinates_zero_iff_closed (n : ℤ) (u : physicalRealSubmodule) :
    physicalGapCoordinates n u = 0 ↔ physicalPeriodicLeft u.val n = physicalPeriodicRight u.val n := by
  rw [← physicalIndexedAction_zero_iff_closed]
  have h := physicalGapCoordinates_radius n u
  have hi := (physicalIndexedAction_nonneg u n).2
  constructor
  · intro hz
    rw [hz] at h
    apply Complex.ext
    · change (physicalIndexedAction n u.val).re = 0
      simp only [Prod.fst_zero,Prod.snd_zero,zero_pow (by decide : (2:ℕ) ≠ 0),zero_add] at h
      linarith
    · exact hi
  · intro hz
    rw [hz,Complex.zero_re,mul_zero] at h
    apply Prod.ext
    · change (physicalGapCoordinates n u).1 = 0
      nlinarith [sq_nonneg (physicalGapCoordinates n u).2]
    · change (physicalGapCoordinates n u).2 = 0
      nlinarith [sq_nonneg (physicalGapCoordinates n u).1]

/-- Global analytic Birkhoff coordinates identify the actual closed-gap locus with a plane. -/
theorem physicalClosedGap_global_chart (n : ℤ) :
    AnalyticOnNhd ℝ intrinsicPhysicalBirkhoffHomeomorph univ ∧
    AnalyticOnNhd ℝ intrinsicPhysicalBirkhoffHomeomorph.symm univ ∧
    intrinsicPhysicalBirkhoffHomeomorph ''
      {u : physicalRealSubmodule | physicalPeriodicLeft u.val n = physicalPeriodicRight u.val n} =
        ((physicalGapEvaluation n).ker : Set PhysicalRealBirkhoffTarget) ∧
    Module.finrank ℝ (PhysicalRealBirkhoffTarget ⧸ (physicalGapEvaluation n).ker) = 2 := by
  refine ⟨intrinsicPhysicalBirkhoffHomeomorph_analytic.1,
    intrinsicPhysicalBirkhoffHomeomorph_analytic.2,?_,physicalGapEvaluation_quotient_finrank n⟩
  ext z
  constructor
  · rintro ⟨u,hu,rfl⟩
    change physicalGapEvaluation n (intrinsicPhysicalBirkhoffHomeomorph u) = 0
    rw [intrinsicPhysicalBirkhoffHomeomorph_apply]
    exact (physicalGapCoordinates_zero_iff_closed n u).mpr hu
  · intro hz
    refine ⟨intrinsicPhysicalBirkhoffHomeomorph.symm z,?_,
      intrinsicPhysicalBirkhoffHomeomorph.apply_symm_apply z⟩
    apply (physicalGapCoordinates_zero_iff_closed n _).mp
    change physicalGapEvaluation n
      (intrinsicPhysicalBirkhoffMap (intrinsicPhysicalBirkhoffHomeomorph.symm z)) = 0
    rw [intrinsicPhysicalBirkhoffHomeomorph_right_inv]
    exact hz

/-- The actual gap-coordinate map is real analytic on the full physical real source. -/
theorem physicalGapCoordinates_analytic (n : ℤ) :
    AnalyticOnNhd ℝ (physicalGapCoordinates n) univ := by
  intro u _
  exact ((physicalGapEvaluation n).analyticAt _).comp
    (intrinsicPhysicalBirkhoffMap_analytic u (mem_univ _))

/-- The physical Birkhoff derivative has its actual inverse derivative as a right inverse. -/
theorem intrinsicPhysicalBirkhoffMap_fderiv_right_inverse (u : physicalRealSubmodule) :
    (fderiv ℝ intrinsicPhysicalBirkhoffMap u).comp
      (fderiv ℝ intrinsicPhysicalBirkhoffHomeomorph.symm (intrinsicPhysicalBirkhoffMap u)) =
      ContinuousLinearMap.id ℝ PhysicalRealBirkhoffTarget := by
  have hi := (intrinsicPhysicalBirkhoffHomeomorph_analytic.2
    (intrinsicPhysicalBirkhoffMap u) (mem_univ _)).differentiableAt.hasFDerivAt
  have hf : HasFDerivAt intrinsicPhysicalBirkhoffMap (fderiv ℝ intrinsicPhysicalBirkhoffMap u)
      (intrinsicPhysicalBirkhoffHomeomorph.symm (intrinsicPhysicalBirkhoffMap u)) := by
    rw [intrinsicPhysicalBirkhoffHomeomorph_left_inv]
    exact (intrinsicPhysicalBirkhoffMap_analytic u (mem_univ _)).differentiableAt.hasFDerivAt
  have hc := hf.comp (intrinsicPhysicalBirkhoffMap u) hi
  have hid : HasFDerivAt (fun z : PhysicalRealBirkhoffTarget => z)
      ((fderiv ℝ intrinsicPhysicalBirkhoffMap u).comp
        (fderiv ℝ intrinsicPhysicalBirkhoffHomeomorph.symm (intrinsicPhysicalBirkhoffMap u)))
      (intrinsicPhysicalBirkhoffMap u) := by
    simpa only [Function.comp_def,intrinsicPhysicalBirkhoffHomeomorph_right_inv] using hc
  exact hid.unique (hasFDerivAt_id _)

/-- The derivative of the physical global inverse also supplies a left inverse. -/
theorem intrinsicPhysicalBirkhoffMap_fderiv_left_inverse (u : physicalRealSubmodule) :
    (fderiv ℝ intrinsicPhysicalBirkhoffHomeomorph.symm (intrinsicPhysicalBirkhoffMap u)).comp
      (fderiv ℝ intrinsicPhysicalBirkhoffMap u) =
      ContinuousLinearMap.id ℝ physicalRealSubmodule := by
  have hi := (intrinsicPhysicalBirkhoffHomeomorph_analytic.2
    (intrinsicPhysicalBirkhoffMap u) (mem_univ _)).differentiableAt.hasFDerivAt
  have hf := (intrinsicPhysicalBirkhoffMap_analytic u (mem_univ _)).differentiableAt.hasFDerivAt
  have hc := hi.comp u hf
  have hid : HasFDerivAt (fun v : physicalRealSubmodule => v)
      ((fderiv ℝ intrinsicPhysicalBirkhoffHomeomorph.symm (intrinsicPhysicalBirkhoffMap u)).comp
        (fderiv ℝ intrinsicPhysicalBirkhoffMap u)) u := by
    simpa only [Function.comp_def,intrinsicPhysicalBirkhoffHomeomorph_left_inv] using hc
  exact hid.unique (hasFDerivAt_id _)

/-- Every physical real Birkhoff derivative is surjective in the original Hilbert norms. -/
theorem intrinsicPhysicalBirkhoffMap_fderiv_surjective (u : physicalRealSubmodule) :
    Function.Surjective (fderiv ℝ intrinsicPhysicalBirkhoffMap u) := by
  intro z
  refine ⟨fderiv ℝ intrinsicPhysicalBirkhoffHomeomorph.symm (intrinsicPhysicalBirkhoffMap u) z,?_⟩
  exact congrArg (fun L : PhysicalRealBirkhoffTarget →L[ℝ] PhysicalRealBirkhoffTarget => L z)
    (intrinsicPhysicalBirkhoffMap_fderiv_right_inverse u)

/-- The full gap-coordinate derivative is the coordinate evaluation of the Birkhoff derivative. -/
theorem physicalGapCoordinates_fderiv (n : ℤ) (u : physicalRealSubmodule) :
    fderiv ℝ (physicalGapCoordinates n) u =
      (physicalGapEvaluation n).comp (fderiv ℝ intrinsicPhysicalBirkhoffMap u) := by
  exact ((physicalGapEvaluation n).hasFDerivAt.comp u
    (intrinsicPhysicalBirkhoffMap_analytic u (mem_univ _)).differentiableAt.hasFDerivAt).fderiv

/-- The literal gap-coordinate map is a submersion at every real physical source. -/
theorem physicalGapCoordinates_fderiv_surjective (n : ℤ) (u : physicalRealSubmodule) :
    Function.Surjective (fderiv ℝ (physicalGapCoordinates n) u) := by
  rw [physicalGapCoordinates_fderiv]
  exact (physicalGapEvaluation_surjective n).comp (intrinsicPhysicalBirkhoffMap_fderiv_surjective u)

/-- The actual differential kernel has two real normal dimensions at every source. -/
theorem physicalGapCoordinates_fderiv_quotient_finrank (n : ℤ) (u : physicalRealSubmodule) :
    Module.finrank ℝ (physicalRealSubmodule ⧸ (fderiv ℝ (physicalGapCoordinates n) u).ker) = 2 := by
  have he := ((fderiv ℝ (physicalGapCoordinates n) u).toLinearMap.quotKerEquivOfSurjective
    (physicalGapCoordinates_fderiv_surjective n u)).finrank_eq
  simpa using he

/-- The source's squared-gap equation is exactly equality of its physical endpoints. -/
theorem physicalSquaredGap_zero_iff_closed (n : ℤ) (u : physicalRealSubmodule) :
    (physicalPeriodicRight u.val n - physicalPeriodicLeft u.val n)^2 = 0 ↔
      physicalPeriodicLeft u.val n = physicalPeriodicRight u.val n := by
  rw [sq_eq_zero_iff,sub_eq_zero,eq_comm]

end NLS.ZakharovShabat
