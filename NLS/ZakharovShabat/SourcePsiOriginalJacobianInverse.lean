import NLS.ZakharovShabat.SourceLemma12_7
import NLS.SequenceSpaces.CompactIdentityFredholm
import NLS.SequenceSpaces.DeletedRealInverse
import NLS.ZakharovShabat.SourcePsiOriginalRealEquation

/-!
# Inverses of the actual original-domain Jacobian

The Fredholm alternative combines the original diagonal-plus-compact
decomposition with injectivity. It yields a continuous complex linear
equivalence equal to the actual Jacobian. Reality of the inverse gives
an equivalence on the real deleted lp space as well.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Fredholm surjectivity from the original compact decomposition and trivial kernel. -/
theorem SourceLemma12_7Data.originalJacobian_bijective
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)} {D : ℤ → Set ℂ} {c : ℝ}
    (H : SourceLemma12_7Data hp hp1 W) (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (hV : IsOpen V) (t : realTypeSourceSubmodule p × RealCoeff p)
    (htW : (t.1:CoeffPair p) ∈ W) (htΩ : t ∈ sourcePsiOriginalOmega V D) (n : ℤ) :
    Function.Bijective (sourcePsiOriginalRootJacobian hp hp1 n
      (Coeff.deleteCoordinateTo n (RealCoeff.complexCLM p t.2)) t.1) := by
  obtain ⟨A,T,hT,hQ,_,_⟩ := H.previous.decomposition hD hV t htW htΩ n
  have hinj := H.injective hD t htW htΩ n
  rw [hQ] at hinj ⊢
  exact Coeff.bijective_add_compact_of_bijective_of_injective
    A.toContinuousLinearMap T A.bijective hT hinj

/-- The continuous complex inverse at an original root-placement point. -/
def SourceLemma12_7Data.originalJacobianEquiv
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)} {D : ℤ → Set ℂ} {c : ℝ}
    (H : SourceLemma12_7Data hp hp1 W) (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (hV : IsOpen V) (t : realTypeSourceSubmodule p × RealCoeff p)
    (htW : (t.1:CoeffPair p) ∈ W) (htΩ : t ∈ sourcePsiOriginalOmega V D) (n : ℤ) :
    DeletedCoeff p n ≃L[ℂ] DeletedCoeff p n :=
  ContinuousLinearEquiv.ofBijective
    (sourcePsiOriginalRootJacobian hp hp1 n (Coeff.deleteCoordinateTo n (RealCoeff.complexCLM p t.2)) t.1)
    (LinearMap.ker_eq_bot.mpr (H.originalJacobian_bijective hD hV t htW htΩ n).1)
    (LinearMap.range_eq_top.mpr (H.originalJacobian_bijective hD hV t htW htΩ n).2)

theorem SourceLemma12_7Data.originalJacobianEquiv_toCLM
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)} {D : ℤ → Set ℂ} {c : ℝ}
    (H : SourceLemma12_7Data hp hp1 W) (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (hV : IsOpen V) (t : realTypeSourceSubmodule p × RealCoeff p)
    (htW : (t.1:CoeffPair p) ∈ W) (htΩ : t ∈ sourcePsiOriginalOmega V D) (n : ℤ) :
    (H.originalJacobianEquiv hD hV t htW htΩ n).toContinuousLinearMap =
      sourcePsiOriginalRootJacobian hp hp1 n (Coeff.deleteCoordinateTo n (RealCoeff.complexCLM p t.2)) t.1 := rfl

theorem SourceLemma12_7Data.originalJacobianEquiv_symm_real
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)} {D : ℤ → Set ℂ} {c : ℝ}
    (H : SourceLemma12_7Data hp hp1 W) (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (hV : IsOpen V) (t : realTypeSourceSubmodule p × RealCoeff p)
    (htW : (t.1:CoeffPair p) ∈ W) (htΩ : t ∈ sourcePsiOriginalOmega V D) (n : ℤ)
    (b : DeletedCoeff p n) (hb : ∀ m : ℤ, ((b:Coeff p) m).im = 0) :
    ∀ m : ℤ, (((H.originalJacobianEquiv hD hV t htW htΩ n).symm b:Coeff p) m).im = 0 := by
  apply Coeff.deletedEquiv_symm_real_of_real_entries hp n _ _ b hb
  intro m k
  exact H.previous.previous.previous.originalJacobianEntry_real t.1 htW t.1.property
    n m k (RealCoeff.complexCLM p t.2) (fun j => by simp)

theorem SourceLemma12_7Data.originalJacobian_real_existsUnique
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)} {D : ℤ → Set ℂ} {c : ℝ}
    (H : SourceLemma12_7Data hp hp1 W) (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (hV : IsOpen V) (t : realTypeSourceSubmodule p × RealCoeff p)
    (htW : (t.1:CoeffPair p) ∈ W) (htΩ : t ∈ sourcePsiOriginalOmega V D) (n : ℤ)
    (b : DeletedCoeff p n) (hb : ∀ m : ℤ, ((b:Coeff p) m).im = 0) :
    ∃! x : DeletedCoeff p n,
      sourcePsiOriginalRootJacobian hp hp1 n (Coeff.deleteCoordinateTo n (RealCoeff.complexCLM p t.2)) t.1 x = b ∧
      ∀ m : ℤ, ((x:Coeff p) m).im = 0 := by
  let e := H.originalJacobianEquiv hD hV t htW htΩ n
  refine ⟨e.symm b,⟨e.apply_symm_apply b,H.originalJacobianEquiv_symm_real hD hV t htW htΩ n b hb⟩,?_⟩
  intro x hx
  apply e.injective
  exact hx.1.trans (e.apply_symm_apply b).symm

/-- The continuous inverse on the real deleted Banach space. -/
def SourceLemma12_7Data.originalJacobianRealEquiv
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)} {D : ℤ → Set ℂ} {c : ℝ}
    (H : SourceLemma12_7Data hp hp1 W) (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (hV : IsOpen V) (t : realTypeSourceSubmodule p × RealCoeff p)
    (htW : (t.1:CoeffPair p) ∈ W) (htΩ : t ∈ sourcePsiOriginalOmega V D) (n : ℤ) :
    RealDeletedCoeff p n ≃L[ℝ] RealDeletedCoeff p n :=
  RealDeletedCoeff.restrictEquiv n (H.originalJacobianEquiv hD hV t htW htΩ n)
    (fun b hb => Coeff.deletedOperator_real_of_real_entries hp n _
      (fun m k => H.previous.previous.previous.originalJacobianEntry_real t.1 htW t.1.property
        n m k (RealCoeff.complexCLM p t.2) (fun j => by simp)) b hb)
    (fun b hb => H.originalJacobianEquiv_symm_real hD hV t htW htΩ n b hb)

theorem SourceLemma12_7Data.originalJacobianRealEquiv_complex
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)} {D : ℤ → Set ℂ} {c : ℝ}
    (H : SourceLemma12_7Data hp hp1 W) (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (hV : IsOpen V) (t : realTypeSourceSubmodule p × RealCoeff p)
    (htW : (t.1:CoeffPair p) ∈ W) (htΩ : t ∈ sourcePsiOriginalOmega V D) (n : ℤ)
    (b : RealDeletedCoeff p n) :
    RealDeletedCoeff.complexCLM n (H.originalJacobianRealEquiv hD hV t htW htΩ n b) =
      sourcePsiOriginalRootJacobian hp hp1 n (Coeff.deleteCoordinateTo n (RealCoeff.complexCLM p t.2)) t.1
        (RealDeletedCoeff.complexCLM n b) :=
  RealDeletedCoeff.complex_restrictEquiv n _ _ _ b

/-- The real equivalence is exactly the derivative of the actual real equation. -/
theorem SourceLemma12_7Data.originalJacobianRealEquiv_toCLM
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)} {D : ℤ → Set ℂ} {c : ℝ}
    (H : SourceLemma12_7Data hp hp1 W) (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (hV : IsOpen V) (t : realTypeSourceSubmodule p × RealCoeff p)
    (htW : (t.1:CoeffPair p) ∈ W) (htΩ : t ∈ sourcePsiOriginalOmega V D) (n : ℤ) :
    (H.originalJacobianRealEquiv hD hV t htW htΩ n).toContinuousLinearMap =
      sourcePsiOriginalRealRootJacobian hp hp1 n (RealDeletedCoeff.deleteCoordinateTo n t.2) t.1 := by
  rw [H.previous.previous.previous.originalRealRootJacobian_eq t.1 htW,
    RealDeletedCoeff.complex_deleteCoordinateTo]
  rfl

/-- Invertibility in the algebra of bounded operators at the original point. -/
theorem SourceLemma12_7Data.originalJacobian_isUnit
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)} {D : ℤ → Set ℂ} {c : ℝ}
    (H : SourceLemma12_7Data hp hp1 W) (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (hV : IsOpen V) (t : realTypeSourceSubmodule p × RealCoeff p)
    (htW : (t.1:CoeffPair p) ∈ W) (htΩ : t ∈ sourcePsiOriginalOmega V D) (n : ℤ) :
    IsUnit (sourcePsiOriginalRootJacobian hp hp1 n
      (Coeff.deleteCoordinateTo n (RealCoeff.complexCLM p t.2)) t.1) :=
  ContinuousLinearMap.isUnit_iff_bijective.mpr (H.originalJacobian_bijective hD hV t htW htΩ n)

/-- A bound at a fixed source and omitted index; no uniformity in n is claimed. -/
theorem SourceLemma12_7Data.originalJacobian_inverse_bound
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)} {D : ℤ → Set ℂ} {c : ℝ}
    (H : SourceLemma12_7Data hp hp1 W) (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (hV : IsOpen V) (t : realTypeSourceSubmodule p × RealCoeff p)
    (htW : (t.1:CoeffPair p) ∈ W) (htΩ : t ∈ sourcePsiOriginalOmega V D) (n : ℤ)
    (b : DeletedCoeff p n) :
    ‖b‖ ≤ ‖(H.originalJacobianEquiv hD hV t htW htΩ n).symm.toContinuousLinearMap‖ *
      ‖sourcePsiOriginalRootJacobian hp hp1 n
        (Coeff.deleteCoordinateTo n (RealCoeff.complexCLM p t.2)) t.1 b‖ := by
  rw [← H.originalJacobianEquiv_toCLM hD hV t htW htΩ n]
  let e := H.originalJacobianEquiv hD hV t htW htΩ n
  simpa only [ContinuousLinearEquiv.coe_coe, e.symm_apply_apply] using
    e.symm.toContinuousLinearMap.le_opNorm (e b)

/-- The corresponding fixed-point bound for the actual real derivative. -/
theorem SourceLemma12_7Data.originalJacobianReal_inverse_bound
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)} {D : ℤ → Set ℂ} {c : ℝ}
    (H : SourceLemma12_7Data hp hp1 W) (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (hV : IsOpen V) (t : realTypeSourceSubmodule p × RealCoeff p)
    (htW : (t.1:CoeffPair p) ∈ W) (htΩ : t ∈ sourcePsiOriginalOmega V D) (n : ℤ)
    (b : RealDeletedCoeff p n) :
    ‖b‖ ≤ ‖(H.originalJacobianRealEquiv hD hV t htW htΩ n).symm.toContinuousLinearMap‖ *
      ‖sourcePsiOriginalRealRootJacobian hp hp1 n (RealDeletedCoeff.deleteCoordinateTo n t.2) t.1 b‖ := by
  rw [← H.originalJacobianRealEquiv_toCLM hD hV t htW htΩ n]
  let e := H.originalJacobianRealEquiv hD hV t htW htΩ n
  simpa only [ContinuousLinearEquiv.coe_coe, e.symm_apply_apply] using
    e.symm.toContinuousLinearMap.le_opNorm (e b)

end NLS.ZakharovShabat
