import NLS.ZakharovShabat.SourceLemma12_6
import NLS.ZakharovShabat.SourcePsiDeletedIndexJacobian

/-!
# Diagonal and compact parts on literal retained indices

The actual root Jacobian on the literal retained-index lp space is an
invertible diagonal plus a compact operator. The diagonal and its inverse
have exact coordinate formulas. The canonical finite output cutoffs have
finite-dimensional range and converge in operator norm after transport.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The original diagonal isomorphism and compact remainder on the literal retained indices. -/
theorem SourceLemma12_6Data.deletedIndexDecomposition
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceLemma12_6Data hp hp1 W)
    {V : Set (CoeffPair p)} {discs : ℤ → Set ℂ} {c : ℝ}
    (hD : SourceIsolatingNeighborhoods hp hp1 V discs c) (hV : IsOpen V)
    (t : realTypeSourceSubmodule p × RealCoeff p) (htW : (t.1:CoeffPair p) ∈ W)
    (htΩ : t ∈ sourcePsiOriginalOmega V discs) (n : ℤ) :
    ∃ D : DeletedIndexCoeff p n ≃L[ℂ] DeletedIndexCoeff p n,
      ∃ T : DeletedIndexCoeff p n →L[ℂ] DeletedIndexCoeff p n, IsCompactOperator T ∧
        sourcePsiDeletedIndexRootJacobian hp hp1 n t.1
          (DeletedCoeff.indexEquiv hp n (Coeff.deleteCoordinateTo n (RealCoeff.complexCLM p t.2))) =
            D.toContinuousLinearMap+T ∧
        (∀ b : DeletedIndexCoeff p n, ∀ m : {m : ℤ // m ≠ n},
          D b m = sourcePsiOriginalJacobianEntry hp hp1 n m.val m.val
            (RealCoeff.complexCLM p t.2) t.1*b m) ∧
        ∀ b : DeletedIndexCoeff p n, ∀ m : {m : ℤ // m ≠ n},
          D.symm b m = (sourcePsiOriginalJacobianEntry hp hp1 n m.val m.val
            (RealCoeff.complexCLM p t.2) t.1)⁻¹*b m := by
  obtain ⟨D,T,hT,hQ,hdiag,hinv⟩ := H.decomposition hD hV t htW htΩ n
  let e := (DeletedCoeff.indexEquiv hp n).toContinuousLinearEquiv
  let D' := (e.symm.trans D).trans e
  let T' := e.toContinuousLinearMap.comp (T.comp e.symm.toContinuousLinearMap)
  refine ⟨D',T',(hT.comp_clm e.symm.toContinuousLinearMap).clm_comp e.toContinuousLinearMap,?_,?_,?_⟩
  · rw [H.previous.previous.deletedIndexRootJacobian_eq t.1 htW n,
      (DeletedCoeff.indexEquiv hp n).symm_apply_apply,hQ]
    ext b m
    change (D (e.symm b)+T (e.symm b) : Coeff p) m.val = _
    rfl
  · intro b m
    change (D (e.symm b):Coeff p) m.val = _
    rw [hdiag]
    congr 1
    exact DeletedCoeff.indexEquiv_symm_apply_other hp n m.val m.property b
  · intro b m
    change (D.symm (e.symm b):Coeff p) m.val = _
    rw [hinv]
    congr 1
    exact DeletedCoeff.indexEquiv_symm_apply_other hp n m.val m.property b

/-- The actual finite output cutoffs also converge in norm on literal retained indices. -/
theorem SourceLemma12_6Data.deletedIndexFiniteRankApproximation
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceLemma12_6Data hp hp1 W)
    {V : Set (CoeffPair p)} {discs : ℤ → Set ℂ} {c : ℝ}
    (hD : SourceIsolatingNeighborhoods hp hp1 V discs c) (hV : IsOpen V)
    (t : realTypeSourceSubmodule p × RealCoeff p) (htW : (t.1:CoeffPair p) ∈ W)
    (htΩ : t ∈ sourcePsiOriginalOmega V discs) (n : ℤ) :
    let T := Coeff.deletedJacobianOffDiagonal n
      (sourcePsiOriginalRootJacobian hp hp1 n
        (Coeff.deleteCoordinateTo n (RealCoeff.complexCLM p t.2)) t.1)
    let e := (DeletedCoeff.indexEquiv hp n).toContinuousLinearEquiv
    let C := e.arrowCongr e
    (∀ s : Finset ℤ, FiniteDimensional ℂ
      (LinearMap.range (C (Coeff.deletedOutputCutoff n T s)).toLinearMap)) ∧
    Tendsto (fun s => C (Coeff.deletedOutputCutoff n T s)) atTop (𝓝 (C T)) ∧
    ∀ s : Finset ℤ, ∀ b : DeletedIndexCoeff p n, ∀ m : {m : ℤ // m ≠ n},
      C (Coeff.deletedOutputCutoff n T s) b m = if m.val ∈ s then C T b m else 0 := by
  dsimp only
  let T := Coeff.deletedJacobianOffDiagonal n
    (sourcePsiOriginalRootJacobian hp hp1 n
      (Coeff.deleteCoordinateTo n (RealCoeff.complexCLM p t.2)) t.1)
  let e := (DeletedCoeff.indexEquiv hp n).toContinuousLinearEquiv
  let C := e.arrowCongr e
  obtain ⟨hfinite,hlim⟩ := H.finiteRankApproximation hD hV t htW htΩ n
  refine ⟨?_,C.continuous.continuousAt.tendsto.comp hlim,?_⟩
  · intro s
    let A := Coeff.deletedOutputCutoff n T s
    let := hfinite s
    apply Submodule.finiteDimensional_of_le
      (S₂ := (LinearMap.range A.toLinearMap).map e.toLinearMap)
    rintro _ ⟨b,rfl⟩
    exact ⟨A (e.symm b),⟨e.symm b,rfl⟩,rfl⟩
  · intro s b m
    change (Coeff.deletedOutputCutoff n T s (e.symm b) : Coeff p) m.val = _
    rw [Coeff.deletedOutputCutoff_apply,Coeff.truncate_apply]
    rfl

end NLS.ZakharovShabat
