import NLS.ZakharovShabat.SourcePsiSelectedJacobianEntry
import NLS.ZakharovShabat.SourcePsiJacobianUniformDiagonalTail

/-!
# Quantitative diagonal tail of the selected psi Jacobian

Beyond a common cutoff, the selected sequence equation uses the same
free-centered circles as the scalar diagonal estimate. Its bounded
root-direction Jacobian therefore inherits the `2 + error` bound.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- On a common distant-row tail, the diagonal matrix entry of the
selected bounded Jacobian differs from `2` by a locally bounded `ℓᵖ`
correction plus the spectral displacement term. It is nonzero on the
real quarter-π localized root locus. -/
theorem exists_local_sourcePsi_selectedJacobian_diagonalUniformEstimate
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (n : ℤ) (a₀ : DeletedCoeff p n) :
    ∃ U : Set (DeletedCoeff p n × CoeffPair p), IsOpen U ∧
      (a₀,φ) ∈ U ∧
      ∃ K : ℕ, ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
        (∀ m : ℤ, K ≤ m.natAbs →
          c m = (Real.pi : ℂ)*m ∧ R m = Real.pi/8) ∧
        ∃ M : ℝ, 0 ≤ M ∧
          ∀ a : DeletedCoeff p n, ∀ ψ : CoeffPair p,
            (a,ψ) ∈ U →
            IsRealType (CoeffPair.toMax p ψ) →
            (∀ j : ℤ, (displacedRoots (a : Coeff p) j).im = 0) →
            ∃ B : Coeff p, ‖B‖ ≤ M ∧
              ∀ m : ℤ, K ≤ m.natAbs → ∀ hmn : m ≠ n,
                (‖((sourcePsiSelectedRootJacobian hp hp1 n c R a ψ
                    (Coeff.deletedSingleCLM n m hmn 1) :
                      DeletedCoeff p n) : Coeff p) m-2‖ ≤
                  4*‖B m‖ +
                    4*(‖sourcePeriodicMidpointDisplacement hp hp1 ψ m‖ +
                      ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖/2) /
                        ‖(Real.pi : ℂ)*((n-m : ℤ) : ℂ)‖) ∧
                ((∀ j : ℤ, ‖(a : Coeff p) j‖ ≤ Real.pi/4) →
                  ((sourcePsiSelectedRootJacobian hp hp1 n c R a ψ
                    (Coeff.deletedSingleCLM n m hmn 1) :
                      DeletedCoeff p n) : Coeff p) m ≠ 0) := by
  obtain ⟨Ueq,hUeqOpen,hbaseEq,Keq,c,R,hchoice,hgeom,hmatrix⟩ :=
    exists_local_sourcePsi_selectedJacobian_matrixFormula
      hp hp1 φ hφ n a₀
  obtain ⟨Utail,hUtailOpen,hbaseTail,Ktail,M,hM,htail⟩ :=
    exists_local_sourcePsi_diagonalJacobian_uniformTail
      hp hp1 φ hφ (a₀ : Coeff p)
  let H : DeletedCoeff p n × CoeffPair p → Coeff p × CoeffPair p :=
    fun t => ((t.1 : Coeff p),t.2)
  have hHcont : Continuous H :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  let U : Set (DeletedCoeff p n × CoeffPair p) :=
    Ueq ∩ H ⁻¹' Utail
  have hUopen : IsOpen U :=
    hUeqOpen.inter (hUtailOpen.preimage hHcont)
  have hbase : (a₀,φ) ∈ U := ⟨hbaseEq,hbaseTail⟩
  let K : ℕ := max (Keq+1) Ktail
  refine ⟨U,hUopen,hbase,K,c,R,?_,M,hM,?_⟩
  · intro m hm
    exact hchoice m (by dsimp [K] at hm; omega)
  intro a ψ hpair hreal hroots
  obtain ⟨B,hBnorm,hB⟩ := htail n a ψ hpair.2 hreal hroots
  refine ⟨B,hBnorm,?_⟩
  intro m hm hmn
  have hmTail : Ktail ≤ m.natAbs := by dsimp [K] at hm; omega
  obtain ⟨hc,hR⟩ := hchoice m (by dsimp [K] at hm; omega)
  have hentry := hmatrix a ψ hpair.1 m m hmn
  constructor
  · rw [hentry]
    simpa only [hc,hR] using (hB m hmTail hmn).1
  · intro hloc
    rw [hentry]
    simpa only [hc,hR] using (hB m hmTail hmn).2 hloc

end NLS.ZakharovShabat
