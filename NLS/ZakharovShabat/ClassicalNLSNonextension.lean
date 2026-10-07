import NLS.ZakharovShabat.SourceHamiltonianSourceObstruction
import NLS.ZakharovShabat.SourceFiniteGapClassicalNLS

/-! # Corollary 22.2(iii) for actual classical NLS solutions

Agreement with the Fourier coefficients of smooth classical NLS solutions
on the finite-gap domain already prevents any extension from being continuous
at a non-Hilbert source. The conclusion uses the forward interval `[0,T]`
and the physical Hamiltonian time orientation, with all spectral data
constructed internally.
-/
noncomputable section
open Set Complex NLS.Fourier
open scoped ENNReal ComplexConjugate
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- Real-type sources are determined by their first Fourier component. -/
theorem realTypeSource_eq_of_fst (φ ψ : realTypeSourceSubmodule p)
    (h : ∀ n : ℤ, φ.val.fst n = ψ.val.fst n) : φ = ψ := by
  apply Subtype.ext
  apply (CoeffPair.toMax p).injective
  apply Prod.ext
  · ext n; exact h n
  · ext n
    change φ.val.snd n = ψ.val.snd n
    exact (φ.property n).trans ((congrArg conj (h (-n))).trans (ψ.property n).symm)

/-- The unique classical finite-gap solution exists at every finite source
exponent greater than one, with the original physical representative. -/
theorem existsUnique_sourceFiniteGap_classicalNLS_trajectory_atExponent
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p)
    (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    ∃! u : ℝ → C(AddCircle (2 : ℝ), ℂ), IsClassicalNLSTrajectory u ∧
      ∀ x : ℝ, u 0 (x : AddCircle (2 : ℝ)) = (sourceFiniteGapPhysicalPair hp hp1 φ hf).1 x := by
  have he := existsUnique_sourceFiniteGap_classicalNLS_trajectory
    (sourceFiniteGapHilbertModel hp hp1 φ hf) (sourceFiniteGapHilbertModel_mem hp hp1 φ hf)
  simpa only [sourceFiniteGapHilbertModel_physicalPair] using he

/-- The uniquely determined physical finite-gap NLS trajectory, without a
chosen spectral atlas in its interface. -/
def sourceFiniteGapClassicalTrajectory (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    ℝ → C(AddCircle (2 : ℝ), ℂ) :=
  (existsUnique_sourceFiniteGap_classicalNLS_trajectory_atExponent hp hp1 φ hf).exists.choose

/-- The chosen trajectory satisfies the PDE and has the exact original initial value. -/
theorem sourceFiniteGapClassicalTrajectory_spec (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    IsClassicalNLSTrajectory (sourceFiniteGapClassicalTrajectory hp hp1 φ hf) ∧
      ∀ x : ℝ, sourceFiniteGapClassicalTrajectory hp hp1 φ hf 0 (x : AddCircle (2 : ℝ)) =
        (sourceFiniteGapPhysicalPair hp hp1 φ hf).1 x :=
  (existsUnique_sourceFiniteGap_classicalNLS_trajectory_atExponent hp hp1 φ hf).exists.choose_spec

namespace SourceAbelianMomentAtlas
variable {W P V B X : Set (CoeffPair 2)}
variable {s t : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

/-- Actual classical Fourier coefficients equal the coefficients of the
Hamiltonian-oriented Hilbert flow of the same finite-gap source. -/
theorem periodOneCoefficient_classicalNLS_eq_hamiltonianFlow
    (H : SourceAbelianMomentAtlas (by simp) (by norm_num) W s)
    (hs : SourcePsiIsolatingComplexExtension (by simp) (by norm_num) P s)
    (E : SourceBirkhoffMapComplexData (by simp) (by norm_num) V B X t)
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p)
    (hf : φ ∈ sourceFiniteGapLocus hp hp1)
    (u : ℝ → C(AddCircle (2 : ℝ), ℂ)) (hu : IsClassicalNLSTrajectory u)
    (hinit : ∀ x : ℝ, u 0 (x : AddCircle (2 : ℝ)) =
      (sourceFiniteGapPhysicalPair hp hp1 φ hf).1 x) (time : ℝ) (n : ℤ) :
    periodOneCoefficient (fun x : ℝ => u time (x : AddCircle (2 : ℝ))) n =
      (H.hamiltonianOrdinarySourceFlow E le_rfl (sourceFiniteGapHilbertModel hp hp1 φ hf) time).val.fst n := by
  have hinit₂ : ∀ x : ℝ, u 0 (x : AddCircle (2 : ℝ)) =
      (sourceFiniteGapPhysicalPair (by simp) (by norm_num) (sourceFiniteGapHilbertModel hp hp1 φ hf)
        (sourceFiniteGapHilbertModel_mem hp hp1 φ hf)).1 x := by
    simpa only [sourceFiniteGapHilbertModel_physicalPair] using hinit
  have he : (fun x : ℝ => u time (x : AddCircle (2 : ℝ))) =
      (H.hamiltonianOrdinaryPhysicalFlow E (sourceFiniteGapHilbertModel hp hp1 φ hf)
        (sourceFiniteGapHilbertModel_mem hp hp1 φ hf) time).1 :=
    funext (H.classicalNLS_eq_hamiltonianOrdinaryPhysicalFlow hs E _ _ u hu hinit₂ time)
  rw [he]
  exact (periodOneCoefficient_sourceFiniteGapPhysicalPair (by simp) (by norm_num) _ _ n).1

end SourceAbelianMomentAtlas

/-- A candidate forward solution map agrees with classical NLS on finite-gap
sources if its first coordinates are their actual physical Fourier integrals.
Existence of the classical solutions is proved independently above; their
energy estimates, spectral trajectories, and agreement are not assumptions. -/
def AgreesWithFiniteGapClassicalNLS (hp : p ≠ ⊤) (hp1 : 1 < p) (T : ℝ)
    (F : realTypeSourceSubmodule p → C(Icc (0 : ℝ) T,realTypeSourceSubmodule q)) : Prop :=
  ∀ φ : realTypeSourceSubmodule p, ∀ hf : φ ∈ sourceFiniteGapLocus hp hp1,
    ∃ u : ℝ → C(AddCircle (2 : ℝ), ℂ), IsClassicalNLSTrajectory u ∧
      (∀ x : ℝ, u 0 (x : AddCircle (2 : ℝ)) = (sourceFiniteGapPhysicalPair hp hp1 φ hf).1 x) ∧
      ∀ time : Icc (0 : ℝ) T, ∀ n : ℤ,
        (F φ time).val.fst n = periodOneCoefficient (fun x : ℝ => u time.val (x : AddCircle (2 : ℝ))) n

/-- Classical agreement is exactly agreement with the uniquely constructed
physical trajectory; it does not depend on a choice of classical solution. -/
theorem agreesWithFiniteGapClassicalNLS_iff (hp : p ≠ ⊤) (hp1 : 1 < p) (T : ℝ)
    (F : realTypeSourceSubmodule p → C(Icc (0 : ℝ) T,realTypeSourceSubmodule q)) :
    AgreesWithFiniteGapClassicalNLS hp hp1 T F ↔
      ∀ φ : realTypeSourceSubmodule p, ∀ hf : φ ∈ sourceFiniteGapLocus hp hp1,
        ∀ time : Icc (0 : ℝ) T, ∀ n : ℤ, (F φ time).val.fst n =
          periodOneCoefficient (fun x : ℝ => sourceFiniteGapClassicalTrajectory hp hp1 φ hf time.val
            (x : AddCircle (2 : ℝ))) n := by
  constructor
  · intro h φ hf time n
    obtain ⟨u,hu,hinit,hcoeff⟩ := h φ hf
    have he : u = sourceFiniteGapClassicalTrajectory hp hp1 φ hf :=
      (existsUnique_sourceFiniteGap_classicalNLS_trajectory_atExponent hp hp1 φ hf).unique
        ⟨hu,hinit⟩ (sourceFiniteGapClassicalTrajectory_spec hp hp1 φ hf)
    simpa only [he] using hcoeff time n
  · intro h φ hf
    exact ⟨sourceFiniteGapClassicalTrajectory hp hp1 φ hf,
      (sourceFiniteGapClassicalTrajectory_spec hp hp1 φ hf).1,
      (sourceFiniteGapClassicalTrajectory_spec hp hp1 φ hf).2,h φ hf⟩

/-- A forward solution-map extension agreeing with actual classical NLS on
finite-gap data is discontinuous at every non-Hilbert source. All atlases
and Birkhoff maps are constructed in the proof. -/
theorem not_continuousAt_classicalNLS_extension
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hq : q ≠ ⊤) (hq1 : 1 < q)
    (h2p : 2 ≤ p) (h2q : 2 ≤ q) (T : ℝ) (hT : 0 < T)
    (φ : realTypeSourceSubmodule p) (hφ : φ ∉ sourceHilbertLocus h2p)
    (F : realTypeSourceSubmodule p → C(Icc (0 : ℝ) T,realTypeSourceSubmodule q))
    (hF : AgreesWithFiniteGapClassicalNLS hp hp1 T F) : ¬ ContinuousAt F φ := by
  obtain ⟨W,P,_,_,hP,hr,s,hs,⟨A⟩⟩ := exists_sourceAbelianMoment_squaredGapAtlas hp hp1
  obtain ⟨V,B,X,t,D⟩ := exists_sourceBirkhoffMap_complex_analytic hp hp1
  obtain ⟨W₂,P₂,_,_,_,_,s₂,hs₂,⟨H⟩⟩ := exists_sourceAbelianMoment_squaredGapAtlas (p := 2) (by simp) (by norm_num)
  obtain ⟨V₂,B₂,X₂,t₂,E⟩ := exists_sourceBirkhoffMap_complex_analytic (p := 2) (by simp) (by norm_num)
  obtain ⟨Vq,Bq,Xq,tq,Q⟩ := exists_sourceBirkhoffMap_complex_analytic hq hq1
  apply A.not_continuousAt_hamiltonianSource_extension hs hP hr D H
    hs₂.toSourcePsiIsolatingComplexExtension E Q h2p h2q T hT φ hφ F
  intro ψ hf time
  obtain ⟨u,hu,hinit,hcoeff⟩ := hF ψ hf
  apply realTypeSource_eq_of_fst
  intro n
  exact (hcoeff time n).trans
    (H.periodOneCoefficient_classicalNLS_eq_hamiltonianFlow hs₂.toSourcePsiIsolatingComplexExtension
      E hp hp1 ψ hf u hu hinit time.val n)

/-- Corollary 22.2(iii), in the dissertation's forward-time form: for
`2 < p ≤ q < ∞`, every classical NLS extension fails continuity at each
source outside the Hilbert locus. Finite-gap classical agreement suffices. -/
theorem classicalNLS_corollary22_2_iii
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (h2p : 2 < p) (hpq : p ≤ q)
    (T : ℝ) (hT : 0 < T) (φ : realTypeSourceSubmodule p)
    (hφ : φ ∉ sourceHilbertLocus h2p.le)
    (F : realTypeSourceSubmodule p → C(Icc (0 : ℝ) T,realTypeSourceSubmodule q))
    (hF : ∀ ψ : realTypeSourceSubmodule p,
      ∀ hf : ψ ∈ sourceFiniteGapLocus hp (lt_trans (by norm_num) h2p),
      ∀ time : Icc (0 : ℝ) T, ∀ n : ℤ, (F ψ time).val.fst n =
        periodOneCoefficient (fun x : ℝ => sourceFiniteGapClassicalTrajectory hp
          (lt_trans (by norm_num) h2p) ψ hf time.val (x : AddCircle (2 : ℝ))) n) :
    ¬ ContinuousAt F φ :=
  not_continuousAt_classicalNLS_extension hp (lt_trans (by norm_num) h2p) hq
    (lt_of_lt_of_le (lt_trans (by norm_num) h2p) hpq) h2p.le (h2p.le.trans hpq) T hT φ hφ F
    ((agreesWithFiniteGapClassicalNLS_iff hp (lt_trans (by norm_num) h2p) T F).mpr hF)

/-- Theorem 18.5(iv): the same physical NLS nonextension conclusion on
`[-T,T]` follows by restricting a proposed extension to forward times. -/
theorem classicalNLS_theorem18_5_iv
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (h2p : 2 < p) (hpq : p ≤ q)
    (T : ℝ) (hT : 0 < T) (φ : realTypeSourceSubmodule p)
    (hφ : φ ∉ sourceHilbertLocus h2p.le)
    (F : realTypeSourceSubmodule p → C(Icc (-T) T,realTypeSourceSubmodule q))
    (hF : ∀ ψ : realTypeSourceSubmodule p,
      ∀ hf : ψ ∈ sourceFiniteGapLocus hp (lt_trans (by norm_num) h2p),
      ∀ time : Icc (-T) T, ∀ n : ℤ, (F ψ time).val.fst n =
        periodOneCoefficient (fun x : ℝ => sourceFiniteGapClassicalTrajectory hp
          (lt_trans (by norm_num) h2p) ψ hf time.val (x : AddCircle (2 : ℝ))) n) :
    ¬ ContinuousAt F φ := by
  intro hcont
  let r : C(Icc (0 : ℝ) T,Icc (-T) T) :=
    ⟨fun time => ⟨time.val,by constructor; linarith [time.property.1]; exact time.property.2⟩,
      by fun_prop⟩
  exact classicalNLS_corollary22_2_iii hp hq h2p hpq T hT φ hφ
    (fun ψ => (F ψ).comp r) (fun ψ hf time n => hF ψ hf (r time) n)
    ((ContinuousMap.continuous_precomp r).continuousAt.comp hcont)

end NLS.ZakharovShabat
