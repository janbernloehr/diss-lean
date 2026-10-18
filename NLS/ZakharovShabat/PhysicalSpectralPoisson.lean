import NLS.ZakharovShabat.PhysicalPoissonAlgebra
import NLS.ZakharovShabat.PhysicalBirkhoffCanonical
import NLS.ZakharovShabat.SourceDiscriminantPoisson

/-! # Commuting physical discriminants and actions

Actual physical discriminants commute on the entire complex L2 space.
The indexed physical actions are analytic on the same Birkhoff domain,
with full differential dI = x dx + y dy. Their canonical brackets give
one-coordinate rotation velocities and action commutation on every real
input, including collapsed gaps.
-/

noncomputable section
open Set Metric MeasureTheory Complex Filter Topology NLS.ComplexAnalysis NLS.Poisson
open scoped ENNReal Classical
namespace NLS.ZakharovShabat

/-- All complex physical L2 discriminants commute under the literal gradient integral. -/
theorem physicalBracket_discriminants (u : IntervalPairL2) (z w : ℂ) :
    physicalBracket (fun v => l2Discriminant v z) (fun v => l2Discriminant v w) u = 0 := by
  rw [physicalBracket_eq_source _ _ _
    ((analyticOnNhd_l2Discriminant_potential z u (mem_univ _)).differentiableAt)
    ((analyticOnNhd_l2Discriminant_potential w u (mem_univ _)).differentiableAt)]
  have he (t : ℂ) : (fun v => l2Discriminant v t) ∘ sourcePhysicalL2 =
      fun φ => canonicalDiscriminant (by simp) (periodOnePotential φ) t := by
    funext φ
    exact (canonicalDiscriminant_eq_l2_source φ t).symm
  rw [he z,he w]
  exact sourceBracket_discriminants_eq_zero (by simp) (by norm_num) le_rfl _ z w

namespace SourceSection14OriginalData
variable {W₀ W V : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
  (D : SourceSection14OriginalData (by simp) (by norm_num) W₀ W V s)
include D

/-- The physical action is the quadratic coordinate radius on a whole complex neighborhood. -/
theorem physicalIndexedAction_eventually (u : IntervalPairL2)
    (hu : u ∈ physicalBirkhoffDomain V) (n : ℤ) :
    physicalIndexedAction n =ᶠ[𝓝 u] (fun v =>
      (1/2:ℂ)*((physicalBirkhoffMap s v).fst n ^ 2+(physicalBirkhoffMap s v).snd n ^ 2)) := by
  filter_upwards [D.physicalBirkhoffDomain_open.mem_nhds hu] with v hv
  have he := D.physicalBirkhoffMap_action_radius v hv n
  linear_combination -(1/2:ℂ)*he

/-- The indexed physical actions are analytic on the same complex physical Birkhoff domain. -/
theorem physicalIndexedAction_analytic (n : ℤ) :
    AnalyticOnNhd ℂ (physicalIndexedAction n) (physicalBirkhoffDomain V) := by
  intro u hu
  have ha := D.physicalBirkhoffMap_analytic u hu
  have hx : AnalyticAt ℂ (fun v => (physicalBirkhoffMap s v).fst n) u :=
    ((sourceCoordinateLeft (p := 2) n).analyticAt _).comp ha
  have hy : AnalyticAt ℂ (fun v => (physicalBirkhoffMap s v).snd n) u :=
    ((sourceCoordinateRight (p := 2) n).analyticAt _).comp ha
  exact (((hx.pow 2).add (hy.pow 2)).const_smul (c := (1/2:ℂ))).congr
    (D.physicalIndexedAction_eventually u hu n).symm

/-- The full complex differential of the physical action retains the original indexed integral. -/
theorem physicalIndexedAction_fderiv (u : IntervalPairL2)
    (hu : u ∈ physicalBirkhoffDomain V) (n : ℤ) :
    fderiv ℂ (physicalIndexedAction n) u =
      (physicalBirkhoffMap s u).fst n • fderiv ℂ (fun v => (physicalBirkhoffMap s v).fst n) u+
      (physicalBirkhoffMap s u).snd n • fderiv ℂ (fun v => (physicalBirkhoffMap s v).snd n) u := by
  have ha := (D.physicalBirkhoffMap_analytic u hu).differentiableAt
  have hx : DifferentiableAt ℂ (fun v => (physicalBirkhoffMap s v).fst n) u :=
    (sourceCoordinateLeft (p := 2) n).differentiableAt.comp u ha
  have hy : DifferentiableAt ℂ (fun v => (physicalBirkhoffMap s v).snd n) u :=
    (sourceCoordinateRight (p := 2) n).differentiableAt.comp u ha
  have hd := ((hx.hasFDerivAt.pow 2).add (hy.hasFDerivAt.pow 2)).const_smul (1/2:ℂ)
  rw [(D.physicalIndexedAction_eventually u hu n).fderiv_eq]
  convert! hd.fderiv using 1
  ext h
  simp only [smul_apply,add_apply,smul_eq_mul]
  norm_num
  ring

/-- Each physical action rotates its coordinate pair with the original Hamiltonian sign. -/
theorem physicalBirkhoffMap_action_brackets (k n : ℤ) (u : physicalRealSubmodule) :
    physicalBracket (fun v => (physicalBirkhoffMap s v).fst n) (physicalIndexedAction k) u.val =
      -(physicalBirkhoffMap s u.val).snd k*(if n = k then 1 else 0) ∧
    physicalBracket (fun v => (physicalBirkhoffMap s v).snd n) (physicalIndexedAction k) u.val =
      (physicalBirkhoffMap s u.val).fst k*(if n = k then 1 else 0) := by
  have hnk := D.physicalBirkhoffMap_canonical n k u
  have hkn := D.physicalBirkhoffMap_canonical k n u
  have hrev : physicalBracket (fun v => (physicalBirkhoffMap s v).snd n)
      (fun v => (physicalBirkhoffMap s v).fst k) u.val = (if n = k then 1 else 0) := by
    rw [physicalBracket_antisymm,hkn.2.1]
    simp only [neg_neg,eq_comm]
  change physicalCotangentBivector _ _ = 0 ∧ physicalCotangentBivector _ _ = _ ∧
    physicalCotangentBivector _ _ = 0 at hnk
  change physicalCotangentBivector _ _ = _ at hrev
  simp only [physicalBracket,D.physicalIndexedAction_fderiv u.val (D.physicalBirkhoffDomain_real u) k,
    physicalCotangentBivector_add_right,physicalCotangentBivector_smul_right,hnk.1,hnk.2.1,hnk.2.2,hrev]
  constructor <;> ring

/-- The physical indexed actions commute, including at collapsed gaps. -/
theorem physicalIndexedActions_commute (n m : ℤ) (u : physicalRealSubmodule) :
    physicalBracket (physicalIndexedAction n) (physicalIndexedAction m) u.val = 0 := by
  have h := D.physicalBirkhoffMap_action_brackets m n u
  change physicalCotangentBivector _ _ = _ ∧ physicalCotangentBivector _ _ = _ at h
  simp only [physicalBracket,D.physicalIndexedAction_fderiv u.val (D.physicalBirkhoffDomain_real u) n,
    physicalCotangentBivector_add_left,physicalCotangentBivector_smul_left,h.1,h.2]
  by_cases hnm : n = m
  · subst m
    simp only [ite_true]
    ring
  · simp only [hnm,ite_false,mul_zero,add_zero]

end SourceSection14OriginalData

/-- Literal physical action commutation requires no supplied normalized Birkhoff family. -/
theorem physicalBracket_indexedActions (n m : ℤ) (u : physicalRealSubmodule) :
    physicalBracket (physicalIndexedAction n) (physicalIndexedAction m) u.val = 0 := by
  obtain ⟨W₀,W,V,s,D⟩ := sourceSection14 (p := 2) (by simp) (by norm_num)
  exact D.toSourceSection14OriginalData.physicalIndexedActions_commute n m u

end NLS.ZakharovShabat
