import NLS.ZakharovShabat.SourceBirkhoffRealActionAngle

/-! # The full sequence map defined by action-angle formulas

The literal square-root/cosine/sine sequences belong to the original lp
spaces and equal the constructed analytic Birkhoff map. They have its
global analytic inverse for `1 < p ≤ 2`, independently of eta choices and
normalized root families. Both directions respect exponent inclusion.
-/

noncomputable section
open Set Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal ComplexOrder
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

namespace SourceSection14OriginalData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W V : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Both literal square-root action-angle sequences belong to the original real lp spaces. -/
theorem real_actionAngle_mem (D : SourceSection14OriginalData hp hp1 W₀ W V s)
    (φ : realTypeSourceSubmodule p) :
    Memℓp (fun n => Real.sqrt (2*(sourceIndexedAction hp hp1 n φ.val).re)*
      Real.cos (sourceAngularOriginalTheta hp hp1 n s φ.val).re) p ∧
    Memℓp (fun n => Real.sqrt (2*(sourceIndexedAction hp hp1 n φ.val).re)*
      Real.sin (sourceAngularOriginalTheta hp hp1 n s φ.val).re) p := by
  have hx : (fun n => Real.sqrt (2*(sourceIndexedAction hp hp1 n φ.val).re)*
      Real.cos (sourceAngularOriginalTheta hp hp1 n s φ.val).re) =
        fun n => (sourceRealBirkhoffMap hp hp1 s φ).1 n :=
    funext (fun n => (D.real_rectangular_formula φ n).1.symm)
  have hy : (fun n => Real.sqrt (2*(sourceIndexedAction hp hp1 n φ.val).re)*
      Real.sin (sourceAngularOriginalTheta hp hp1 n s φ.val).re) =
        fun n => (sourceRealBirkhoffMap hp hp1 s φ).2 n :=
    funext (fun n => (D.real_rectangular_formula φ n).2.symm)
  rw [hx,hy]
  exact ⟨lp.memℓp _,lp.memℓp _⟩

/-- Define the real sequence map directly by the literal action-angle formulas. -/
def realActionAngleMap (D : SourceSection14OriginalData hp hp1 W₀ W V s)
    (φ : realTypeSourceSubmodule p) : RealCoeff p × RealCoeff p :=
  (⟨fun n => Real.sqrt (2*(sourceIndexedAction hp hp1 n φ.val).re)*
      Real.cos (sourceAngularOriginalTheta hp hp1 n s φ.val).re,(D.real_actionAngle_mem φ).1⟩,
    ⟨fun n => Real.sqrt (2*(sourceIndexedAction hp hp1 n φ.val).re)*
      Real.sin (sourceAngularOriginalTheta hp hp1 n s φ.val).re,(D.real_actionAngle_mem φ).2⟩)

/-- The formula-defined map is exactly the previously constructed analytic map. -/
theorem realActionAngleMap_eq (D : SourceSection14OriginalData hp hp1 W₀ W V s) :
    D.realActionAngleMap = sourceRealBirkhoffMap hp hp1 s := by
  funext φ
  apply Prod.ext <;> ext n
  · exact (D.real_rectangular_formula φ n).1.symm
  · exact (D.real_rectangular_formula φ n).2.symm

/-- The full literal action-angle map is analytic even where its individual angles are undefined. -/
theorem realActionAngleMap_analytic (D : SourceSection14OriginalData hp hp1 W₀ W V s) :
    AnalyticOnNhd ℝ D.realActionAngleMap univ := by
  rw [D.realActionAngleMap_eq]
  exact D.complex.real_map_analytic

/-- Replacing every eta integral by another admissible choice preserves the full output. -/
theorem realActionAngleMap_eta_choices (D : SourceSection14OriginalData hp hp1 W₀ W V s)
    (φ : realTypeSourceSubmodule p) (v : ℤ → ℂ)
    (hv : ∀ n, sourcePeriodicGapDisplacement hp hp1 φ.val n ≠ 0 →
      v n ∈ sourceAngularOriginalEtaIntegralValues hp hp1 n s φ.val) :
    (fun n => (D.realActionAngleMap φ).1 n) =
      (fun n => Real.sqrt (2*(sourceIndexedAction hp hp1 n φ.val).re)*
        Real.cos (v n+sourceAngularBetaCorrection hp hp1 n s φ.val).re) ∧
    (fun n => (D.realActionAngleMap φ).2 n) =
      (fun n => Real.sqrt (2*(sourceIndexedAction hp hp1 n φ.val).re)*
        Real.sin (v n+sourceAngularBetaCorrection hp hp1 n s φ.val).re) := by
  rw [D.realActionAngleMap_eq]
  exact ⟨funext (fun n => (D.real_rectangular_formula_of_eta φ n (v n) (hv n)).1),
    funext (fun n => (D.real_rectangular_formula_of_eta φ n (v n) (hv n)).2)⟩

/-- The formula-defined map has the existing global analytic inverse in the onto range. -/
def realActionAngleHomeomorph (D : SourceSection14OriginalData hp hp1 W₀ W V s) (hp2 : p ≤ 2) :
    realTypeSourceSubmodule p ≃ₜ (RealCoeff p × RealCoeff p) where
  toFun := D.realActionAngleMap
  invFun := (D.complex.realHomeomorph hp2).symm
  left_inv := by
    intro φ
    rw [D.realActionAngleMap_eq]
    exact (D.complex.realHomeomorph hp2).symm_apply_apply φ
  right_inv := by
    intro z
    rw [D.realActionAngleMap_eq]
    exact (D.complex.realHomeomorph hp2).apply_symm_apply z
  continuous_toFun := by
    rw [D.realActionAngleMap_eq]
    exact (D.complex.realHomeomorph hp2).continuous
  continuous_invFun := (D.complex.realHomeomorph hp2).symm.continuous

/-- Its inverse is the previously constructed global analytic inverse. -/
@[simp] theorem realActionAngleHomeomorph_symm_apply
    (D : SourceSection14OriginalData hp hp1 W₀ W V s) (hp2 : p ≤ 2) (z : RealCoeff p × RealCoeff p) :
    (D.realActionAngleHomeomorph hp2).symm z = (D.complex.realHomeomorph hp2).symm z := rfl

/-- Both directions of the literal action-angle homeomorphism are analytic. -/
theorem realActionAngleHomeomorph_analytic (D : SourceSection14OriginalData hp hp1 W₀ W V s)
    (hp2 : p ≤ 2) :
    AnalyticOnNhd ℝ (D.realActionAngleHomeomorph hp2) univ ∧
      AnalyticOnNhd ℝ (D.realActionAngleHomeomorph hp2).symm univ :=
  ⟨D.realActionAngleMap_analytic,D.complex.realHomeomorph_symm_analytic hp2⟩


/-- Literal action-angle maps commute with exponent inclusion for independent families. -/
theorem realActionAngleMap_exponent {q : ℝ≥0∞} [Fact (1 ≤ q)]
    {hq : q ≠ ⊤} {hq1 : 1 < q} {A B C : Set (CoeffPair q)}
    {t : (n : ℤ) → CoeffPair q → DeletedCoeff q n}
    (D : SourceSection14OriginalData hp hp1 W₀ W V s)
    (E : SourceSection14OriginalData hq hq1 A B C t) (hpq : p ≤ q)
    (φ : realTypeSourceSubmodule p) :
    ((RealCoeff.exponentInclusion hpq).prodMap (RealCoeff.exponentInclusion hpq))
      (D.realActionAngleMap φ) = E.realActionAngleMap (realTypeSourceExponentInclusion hpq φ) := by
  rw [D.realActionAngleMap_eq,E.realActionAngleMap_eq]
  exact D.complex.real_map_exponent E.complex hpq φ

/-- The literal map is independent of the normalized root family used to construct it. -/
theorem realActionAngleMap_family {A B C : Set (CoeffPair p)}
    {t : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    (D : SourceSection14OriginalData hp hp1 W₀ W V s)
    (E : SourceSection14OriginalData hp hp1 A B C t) : D.realActionAngleMap = E.realActionAngleMap := by
  funext φ
  have hφ : realTypeSourceExponentInclusion (le_refl p) φ = φ := by
    apply Subtype.ext
    apply (WithLp.equiv p _).injective
    apply Prod.ext <;> ext n <;> rfl
  have h := D.realActionAngleMap_exponent E (le_refl p) φ
  rw [hφ] at h
  apply Prod.ext <;> ext n
  · exact congrArg (fun z : RealCoeff p × RealCoeff p => z.1 n) h
  · exact congrArg (fun z : RealCoeff p × RealCoeff p => z.2 n) h

/-- The global inverses of the literal maps commute with exponent inclusion. -/
theorem realActionAngleHomeomorph_symm_exponent {q : ℝ≥0∞} [Fact (1 ≤ q)]
    {hq : q ≠ ⊤} {hq1 : 1 < q} {A B C : Set (CoeffPair q)}
    {t : (n : ℤ) → CoeffPair q → DeletedCoeff q n}
    (D : SourceSection14OriginalData hp hp1 W₀ W V s)
    (E : SourceSection14OriginalData hq hq1 A B C t)
    (hpq : p ≤ q) (hp2 : p ≤ 2) (hq2 : q ≤ 2) (z : RealCoeff p × RealCoeff p) :
    realTypeSourceExponentInclusion hpq ((D.realActionAngleHomeomorph hp2).symm z) =
      (E.realActionAngleHomeomorph hq2).symm
        (((RealCoeff.exponentInclusion hpq).prodMap (RealCoeff.exponentInclusion hpq)) z) :=
  D.complex.realHomeomorph_symm_exponent E.complex hp2 hq2 hpq z

end SourceSection14OriginalData

end NLS.ZakharovShabat
