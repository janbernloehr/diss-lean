import NLS.ZakharovShabat.SourcePsiSelectedJacobianDiagonalTail
import NLS.ZakharovShabat.SourcePsiSelectedJacobianOffDiagonalTail

/-!
# One selected psi Jacobian with both tail estimates

The diagonal and off-diagonal scalar estimates can be restricted to
one neighborhood of the real-type base point. Beyond one cutoff, both
use the free-centered contours of the same selected sequence equation.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- One bounded selected-root Jacobian has nonzero diagonal entries
and an `ℓᵖ` off-diagonal row majorant on the same distant rows. The
contour family, source neighborhood, row cutoff, and norm bound are
common to both conclusions. -/
theorem exists_local_sourcePsi_selectedJacobian_combinedUniformTail
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
            (∀ j : ℤ, ‖(a : Coeff p) j‖ ≤ Real.pi/4) →
            ∃ B : Coeff p, ‖B‖ ≤ M ∧
              ∀ m : ℤ, K ≤ m.natAbs → ∀ hmn : m ≠ n,
                ((sourcePsiSelectedRootJacobian hp hp1 n c R a ψ
                  (Coeff.deletedSingleCLM n m hmn 1) :
                    DeletedCoeff p n) : Coeff p) m ≠ 0 ∧
                ∀ k : ℤ, ∀ hkn : k ≠ n, ∀ _hmk : m ≠ k,
                  ‖((sourcePsiSelectedRootJacobian hp hp1 n c R a ψ
                    (Coeff.deletedSingleCLM n k hkn 1) :
                      DeletedCoeff p n) : Coeff p) m‖ ≤
                    ‖sourcePsiOffDiagonalRowMajorant hp hp1
                      (a : Coeff p) ψ B m‖ /
                      ‖((m-k : ℤ) : ℂ)‖ := by
  obtain ⟨Ueq,hUeqOpen,hbaseEq,Keq,c,R,hchoice,hgeom,hmatrix⟩ :=
    exists_local_sourcePsi_selectedJacobian_matrixFormula
      hp hp1 φ hφ n a₀
  obtain ⟨Udiag,hUdiagOpen,hbaseDiag,Kdiag,hdiag⟩ :=
    exists_local_sourcePsi_diagonalJacobian_uniformNonzeroTail
      hp hp1 φ hφ (a₀ : Coeff p)
  obtain ⟨Uoff,hUoffOpen,hbaseOff,Koff,M,hM,hoff⟩ :=
    exists_local_sourcePsi_offDiagonalJacobian_uniformTail
      hp hp1 φ hφ (a₀ : Coeff p)
  let H : DeletedCoeff p n × CoeffPair p → Coeff p × CoeffPair p :=
    fun t => ((t.1 : Coeff p),t.2)
  have hHcont : Continuous H :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  let U : Set (DeletedCoeff p n × CoeffPair p) :=
    Ueq ∩ H ⁻¹' (Udiag ∩ Uoff)
  have hUopen : IsOpen U :=
    hUeqOpen.inter ((hUdiagOpen.inter hUoffOpen).preimage hHcont)
  have hbase : (a₀,φ) ∈ U :=
    ⟨hbaseEq,⟨hbaseDiag,hbaseOff⟩⟩
  let K : ℕ := max (Keq+1) (max Kdiag Koff)
  refine ⟨U,hUopen,hbase,K,c,R,?_,M,hM,?_⟩
  · intro m hm
    exact hchoice m (by dsimp [K] at hm; omega)
  intro a ψ hpair hreal hroots hloc
  obtain ⟨B,hBnorm,hB⟩ :=
    hoff n a ψ hpair.2.2 hreal hroots hloc
  refine ⟨B,hBnorm,?_⟩
  intro m hm hmn
  have hmDiag : Kdiag ≤ m.natAbs := by dsimp [K] at hm; omega
  have hmOff : Koff ≤ m.natAbs := by dsimp [K] at hm; omega
  obtain ⟨hc,hR⟩ := hchoice m (by dsimp [K] at hm; omega)
  constructor
  · rw [hmatrix a ψ hpair.1 m m hmn]
    simpa only [hc,hR] using
      hdiag n a ψ hpair.2.1 hreal hroots hloc m hmDiag hmn
  · intro k hkn hmk
    rw [hmatrix a ψ hpair.1 m k hkn]
    simpa only [hc,hR] using hB m hmOff hmn k hkn hmk

end NLS.ZakharovShabat
