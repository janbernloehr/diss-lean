import NLS.ZakharovShabat.PhysicalPoissonBracket
import NLS.ZakharovShabat.PhysicalBirkhoffIntrinsicProperties
import NLS.ZakharovShabat.SourceBirkhoffLemma15_3

/-! # Canonical identities for the physical Birkhoff map

The complex extension of the intrinsic physical action-angle map satisfies
the literal physical Poisson integral identities at every real input,
including collapsed gaps. The mixed x,y bracket is minus the Kronecker
delta, with the positive sine orientation used by the physical map.
-/

noncomputable section
open Set MeasureTheory Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.ZakharovShabat
open NLS.Poisson NLS.Fourier

namespace SourceSection14OriginalData
variable {W₀ W V : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
  (D : SourceSection14OriginalData (by simp) (by norm_num) W₀ W V s)
include D

/-- The complex extension satisfies the literal physical integral brackets at every real input. -/
theorem physicalBirkhoffMap_canonical (n m : ℤ) (u : physicalRealSubmodule) :
    physicalBracket (fun v => (physicalBirkhoffMap s v).fst n)
      (fun v => (physicalBirkhoffMap s v).fst m) u.val = 0 ∧
    physicalBracket (fun v => (physicalBirkhoffMap s v).fst n)
      (fun v => (physicalBirkhoffMap s v).snd m) u.val = -(if n = m then 1 else 0) ∧
    physicalBracket (fun v => (physicalBirkhoffMap s v).snd n)
      (fun v => (physicalBirkhoffMap s v).snd m) u.val = 0 := by
  have ha := (D.physicalBirkhoffMap_analytic u.val (D.physicalBirkhoffDomain_real u)).differentiableAt
  have hx (k : ℤ) : DifferentiableAt ℂ (fun v => (physicalBirkhoffMap s v).fst k) u.val :=
    (sourceCoordinateLeft (p := 2) k).differentiableAt.comp u.val ha
  have hy (k : ℤ) : DifferentiableAt ℂ (fun v => (physicalBirkhoffMap s v).snd k) u.val :=
    (sourceCoordinateRight (p := 2) k).differentiableAt.comp u.val ha
  have hX (k : ℤ) : (fun v => (physicalBirkhoffMap s v).fst k) ∘ sourcePhysicalL2 =
      fun φ => (sourceBirkhoffMap (by simp) (by norm_num) s φ).1 k := by
    funext φ
    simp only [Function.comp_apply,physicalBirkhoffMap,← sourcePhysicalL2Equiv_apply,
      LinearIsometryEquiv.symm_apply_apply]
    rfl
  have hY (k : ℤ) : (fun v => (physicalBirkhoffMap s v).snd k) ∘ sourcePhysicalL2 =
      fun φ => (sourceBirkhoffMap (by simp) (by norm_num) s φ).2 k := by
    funext φ
    simp only [Function.comp_apply,physicalBirkhoffMap,← sourcePhysicalL2Equiv_apply,
      LinearIsometryEquiv.symm_apply_apply]
    rfl
  rw [physicalBracket_eq_source _ _ _ (hx n) (hx m),
    physicalBracket_eq_source _ _ _ (hx n) (hy m),
    physicalBracket_eq_source _ _ _ (hy n) (hy m),hX n,hX m,hY n,hY m]
  exact D.complex.sourceBracket_canonical le_rfl n m (realSourcePhysicalL2Equiv.symm u)

end SourceSection14OriginalData

/-- The intrinsic physical map has a complex extension with the actual physical canonical brackets. -/
theorem intrinsicPhysicalBirkhoffMap_canonical_extension :
    ∃ U : Set IntervalPairL2, ∃ F : IntervalPairL2 → CoeffPair 2,
      IsOpen U ∧ (∀ u : physicalRealSubmodule, u.val ∈ U) ∧ AnalyticOnNhd ℂ F U ∧
      (∀ u : physicalRealSubmodule, physicalRealTargetComplex (intrinsicPhysicalBirkhoffMap u) = F u.val) ∧
      ∀ (u : physicalRealSubmodule) (n m : ℤ),
        physicalBracket (fun v => (F v).fst n) (fun v => (F v).fst m) u.val = 0 ∧
        physicalBracket (fun v => (F v).fst n) (fun v => (F v).snd m) u.val = -(if n = m then 1 else 0) ∧
        physicalBracket (fun v => (F v).snd n) (fun v => (F v).snd m) u.val = 0 := by
  obtain ⟨W₀,W,V,s,D⟩ := sourceSection14 (p := 2) (by simp) (by norm_num)
  let A := D.toSourceSection14OriginalData
  exact ⟨physicalBirkhoffDomain V,physicalBirkhoffMap s,A.physicalBirkhoffDomain_open,
    A.physicalBirkhoffDomain_real,A.physicalBirkhoffMap_analytic,A.intrinsicPhysicalBirkhoffMap_complex,
    fun u n m => A.physicalBirkhoffMap_canonical n m u⟩

end NLS.ZakharovShabat
