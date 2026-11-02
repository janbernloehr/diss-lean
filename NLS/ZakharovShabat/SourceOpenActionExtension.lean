import NLS.ZakharovShabat.SourceOpenActionDescent
import NLS.SequenceSpaces.RealActionBallGluing

/-! # Analytic action extensions of locally defined source functions

An analytic scalar function invariant on the real action fibers in an
open source domain descends to an open action domain. Every nonnegative
action in that domain has a real representative in the original domain;
these representatives give compatibility and uniqueness of the gluing.
-/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderTriple p q]
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B X U : Set (CoeffPair p)}
  {t : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Action balls with real lifts inside the prescribed source domain
and recovery for every real representative in that domain. -/
theorem exists_scalar_realActionBalls_on
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t)
    (f : CoeffPair p → ℂ) (hU : IsOpen U) (hf : AnalyticOnNhd ℂ f U)
    (hinv : ∀ a b : realTypeSourceSubmodule p, a.val ∈ U → b.val ∈ U →
      b ∈ sourceRealActionLevelSet hp hp1 a → f b.val = f a.val)
    (φ : realTypeSourceSubmodule p) (hφ : φ.val ∈ U) :
    ∃ R : ℝ, 0 < R ∧
      (∀ b ∈ ball (sourceActionSequence (q := q) hp hp1 t φ.val) R,
        ∃ ψ ∈ X ∩ U, sourceActionSequence (q := q) hp hp1 t ψ = b) ∧
      (∀ b ∈ ball (sourceActionSequence (q := q) hp hp1 t φ.val) R,
        b ∈ Coeff.nonnegativeLocus q → ∃ ψ : realTypeSourceSubmodule p,
          ψ.val ∈ U ∧ sourceActionSequence (q := q) hp hp1 t ψ.val = b) ∧
      ∃ g : Coeff q → ℂ,
        AnalyticOnNhd ℂ g (ball (sourceActionSequence (q := q) hp hp1 t φ.val) R) ∧
        ∀ ψ : realTypeSourceSubmodule p, ψ.val ∈ U →
          sourceActionSequence (q := q) hp hp1 t ψ.val ∈
            ball (sourceActionSequence (q := q) hp hp1 t φ.val) R →
          g (sourceActionSequence (q := q) hp hp1 t ψ.val) = f ψ.val := by
  obtain ⟨C,Z,T,g,hZ,hbase,hZC,hT,himage,hg,hrec⟩ :=
    D.exists_local_scalar_action_factor_on (q := q) f hU hf hinv φ hφ
  have hcenter : sourceActionSequence (q := q) hp hp1 t φ.val ∈ T := by
    rw [← himage]
    exact ⟨_,hbase,rfl⟩
  obtain ⟨R,hR,hball,hlift⟩ := D.exists_realAction_ball φ Z hZ hbase T hT hcenter
  refine ⟨R,hR,?_,?_,g,hg.mono hball,?_⟩
  · intro b hb
    obtain ⟨z,hz,he⟩ := himage.symm ▸ hball hb
    exact ⟨C.inverse z,C.image_subset (hZC hz),(C.actionSequence_eq z (hZC hz)).trans he⟩
  · intro b hb hpos
    obtain ⟨z,⟨hz,hzr⟩,he⟩ := hlift ⟨hb,hpos⟩
    obtain ⟨w,hw⟩ := (Coeff.mem_realPairLocus_iff z).mp hzr
    have hreal : C.inverse z ∈ realTypeSourceLocus p := by
      rw [← hw]
      exact C.real_preserving w (hw.symm ▸ hZC hz)
    exact ⟨⟨C.inverse z,hreal⟩,(C.image_subset (hZC hz)).2,
      (C.actionSequence_eq z (hZC hz)).trans he⟩
  · intro ψ hψU hψ
    exact C.recover_of_real_action_lift_on Z hZC f g hinv hrec ψ hψU
      (hlift ⟨hψ,D.actionSequence_mem_nonnegativeLocus ψ⟩)

/-- An actual analytic action extension on a union of complex action
balls. It is uniquely determined there by all real sources in `U`.
No invariance outside `U`, nonzero-action hypothesis, or finite-gap
assumption is needed. -/
theorem exists_scalar_action_extension_on
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t)
    (f : CoeffPair p → ℂ) (hU : IsOpen U) (hf : AnalyticOnNhd ℂ f U)
    (hinv : ∀ a b : realTypeSourceSubmodule p, a.val ∈ U → b.val ∈ U →
      b ∈ sourceRealActionLevelSet hp hp1 a → f b.val = f a.val) :
    ∃ V : Set (Coeff q), ∃ G : Coeff q → ℂ, IsOpen V ∧
      (∀ φ : realTypeSourceSubmodule p, φ.val ∈ U → sourceActionSequence (q := q) hp hp1 t φ.val ∈ V) ∧
      (∀ b ∈ V, ∃ ψ ∈ X ∩ U, sourceActionSequence (q := q) hp hp1 t ψ = b) ∧
      (∀ b ∈ V, b ∈ Coeff.nonnegativeLocus q → ∃ ψ : realTypeSourceSubmodule p,
        ψ.val ∈ U ∧ sourceActionSequence (q := q) hp hp1 t ψ.val = b) ∧
      AnalyticOnNhd ℂ G V ∧
      (∀ φ : realTypeSourceSubmodule p, φ.val ∈ U →
        G (sourceActionSequence (q := q) hp hp1 t φ.val) = f φ.val) ∧
      (∀ H : Coeff q → ℂ, AnalyticOnNhd ℂ H V →
        (∀ φ : realTypeSourceSubmodule p, φ.val ∈ U →
          H (sourceActionSequence (q := q) hp hp1 t φ.val) = f φ.val) → EqOn H G V) := by
  classical
  let α := {φ : realTypeSourceSubmodule p // φ.val ∈ U}
  have hballs (φ : α) := D.exists_scalar_realActionBalls_on (q := q) f hU hf hinv φ.val φ.property
  choose R hR hcomplex hlift hlocal using hballs
  let a : α → Coeff q := fun φ => sourceActionSequence hp hp1 t φ.val.val
  let V := ⋃ φ, ball (a φ) (R φ)
  have ha (φ : α) : a φ ∈ Coeff.nonnegativeLocus q :=
    D.actionSequence_mem_nonnegativeLocus φ.val
  have hreal : ∀ φ b, b ∈ ball (a φ) (R φ) → b ∈ Coeff.nonnegativeLocus q → ∃ ψ, a ψ = b := by
    intro φ b hb hpos
    obtain ⟨ψ,hψ,he⟩ := hlift φ b hb hpos
    exact ⟨⟨ψ,hψ⟩,he⟩
  have hrec : ∀ φ, ∃ g : Coeff q → ℂ, AnalyticOnNhd ℂ g (ball (a φ) (R φ)) ∧
      ∀ ψ, a ψ ∈ ball (a φ) (R φ) → g (a ψ) = f ψ.val.val := by
    intro φ
    obtain ⟨g,hg,hgRec⟩ := hlocal φ
    exact ⟨g,hg,fun ψ hψ => hgRec ψ.val ψ.property hψ⟩
  obtain ⟨G,hG,hGrec⟩ := Coeff.exists_analytic_gluing_of_real_action_ball_recovery
    hp a R (fun φ => f φ.val.val) ha hR hreal hrec
  refine ⟨V,G,isOpen_iUnion (fun _ => isOpen_ball),?_,?_,?_,hG,?_,?_⟩
  · intro φ hφ
    exact mem_iUnion.mpr ⟨⟨φ,hφ⟩,mem_ball_self (hR ⟨φ,hφ⟩)⟩
  · intro b hb
    obtain ⟨φ,hφ⟩ := mem_iUnion.mp hb
    exact hcomplex φ b hφ
  · intro b hb hpos
    obtain ⟨φ,hφ⟩ := mem_iUnion.mp hb
    exact hlift φ b hφ hpos
  · intro φ hφ
    exact hGrec ⟨φ,hφ⟩
  · intro H hH hHrec
    exact Coeff.eqOn_of_real_action_ball_agreement hp a R ha hR hreal H G hH hG
      (fun φ => (hHrec φ.val φ.property).trans (hGrec φ).symm)

end NLS.ZakharovShabat.SourceBirkhoffMapComplexData
