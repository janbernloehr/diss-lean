import NLS.ZakharovShabat.SourcePsiSelectedJacobianEntry
import NLS.ZakharovShabat.SourcePsiJacobianUniformDiagonalTail

/-!
# Nonzero diagonal tail of the selected psi Jacobian

The selected sequence-valued equation and the scalar gap estimates may
use different contours on finitely many rows. Their contours agree on
the free-centered tail. This transfers the scalar diagonal nonvanishing
theorem to matrix entries of the bounded Fréchet derivative.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Near a real-type source, the actual bounded root-direction Jacobian
of the selected sequence equation has a nonzero diagonal on every
sufficiently distant retained row, on the real quarter-π root locus.
The row cutoff is uniform in the deleted index and in the parameters
of the chosen neighborhood. -/
theorem exists_local_sourcePsi_selectedJacobian_uniformNonzeroDiagonalTail
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (n : ℤ) (a₀ : DeletedCoeff p n) :
    ∃ U : Set (DeletedCoeff p n × CoeffPair p), IsOpen U ∧
      (a₀,φ) ∈ U ∧
      ∃ K : ℕ, ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
        (∀ m : ℤ, K ≤ m.natAbs →
          c m = (Real.pi : ℂ)*m ∧ R m = Real.pi/8) ∧
        ∀ a : DeletedCoeff p n, ∀ ψ : CoeffPair p,
          (a,ψ) ∈ U →
          IsRealType (CoeffPair.toMax p ψ) →
          (∀ j : ℤ, (displacedRoots (a : Coeff p) j).im = 0) →
          (∀ j : ℤ, ‖(a : Coeff p) j‖ ≤ Real.pi/4) →
          ∀ m : ℤ, K ≤ m.natAbs → ∀ hmn : m ≠ n,
            ((sourcePsiSelectedRootJacobian hp hp1 n c R a ψ
              (Coeff.deletedSingleCLM n m hmn 1) : DeletedCoeff p n) : Coeff p) m
              ≠ 0 := by
  obtain ⟨Ueq,hUeqOpen,hbaseEq,Keq,c,R,_,hchoice,hgeom,hmatrix⟩ :=
    exists_local_sourcePsi_selectedJacobian_matrixFormula
      hp hp1 φ hφ n a₀
  obtain ⟨Utail,hUtailOpen,hbaseTail,Ktail,htail⟩ :=
    exists_local_sourcePsi_diagonalJacobian_uniformNonzeroTail
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
  refine ⟨U,hUopen,hbase,K,c,R,?_,?_⟩
  · intro m hm
    exact hchoice m (by dsimp [K] at hm; omega)
  intro a ψ hpair hreal hroots hloc m hm hmn
  have hmTail : Ktail ≤ m.natAbs := by dsimp [K] at hm; omega
  obtain ⟨hc,hR⟩ := hchoice m (by dsimp [K] at hm; omega)
  have hentry := hmatrix a ψ hpair.1 m m hmn
  rw [hentry]
  simpa only [hc,hR] using
    htail n a ψ hpair.2 hreal hroots hloc m hmTail hmn

end NLS.ZakharovShabat
