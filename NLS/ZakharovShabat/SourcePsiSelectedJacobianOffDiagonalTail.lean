import NLS.ZakharovShabat.SourcePsiSelectedJacobianEntry
import NLS.ZakharovShabat.SourcePsiJacobianUniformOffDiagonalTail

/-!
# Off-diagonal tail of the selected psi Jacobian

The selected sequence equation and the scalar off-diagonal estimate
have the same free-centered contour on all sufficiently distant rows.
Thus the scalar row majorant controls matrix entries of the bounded
Fréchet derivative itself.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The selected sequence-valued psi Jacobian has the quantitative
off-diagonal row estimate on a common tail. The row majorant is in
`ℓᵖ` and has locally bounded norm. The source neighborhood and cutoff
are uniform in the deleted index; here that index is fixed by the
domain of the bounded operator. -/
theorem exists_local_sourcePsi_selectedJacobian_offDiagonalUniformTail
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
              ∀ m : ℤ, K ≤ m.natAbs → ∀ _hmn : m ≠ n,
                ∀ k : ℤ, ∀ hkn : k ≠ n, ∀ _hmk : m ≠ k,
                  ‖((sourcePsiSelectedRootJacobian hp hp1 n c R a ψ
                    (Coeff.deletedSingleCLM n k hkn 1) :
                      DeletedCoeff p n) : Coeff p) m‖ ≤
                    ‖sourcePsiOffDiagonalRowMajorant hp hp1
                      (a : Coeff p) ψ B m‖ /
                      ‖((m-k : ℤ) : ℂ)‖ := by
  obtain ⟨Ueq,hUeqOpen,hbaseEq,Keq,c,R,hchoice,hmatrix⟩ :=
    exists_local_sourcePsi_selectedJacobian_matrixFormula
      hp hp1 φ hφ n a₀
  obtain ⟨Utail,hUtailOpen,hbaseTail,Ktail,M,hM,htail⟩ :=
    exists_local_sourcePsi_offDiagonalJacobian_uniformTail
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
  intro a ψ hpair hreal hroots hloc
  obtain ⟨B,hBnorm,hB⟩ :=
    htail n a ψ hpair.2 hreal hroots hloc
  refine ⟨B,hBnorm,?_⟩
  intro m hm hmn k hkn hmk
  have hmTail : Ktail ≤ m.natAbs := by dsimp [K] at hm; omega
  obtain ⟨hc,hR⟩ := hchoice m (by dsimp [K] at hm; omega)
  have hentry := hmatrix a ψ hpair.1 m k hkn
  rw [hentry]
  simpa only [hc,hR] using hB m hmTail hmn k hkn hmk

end NLS.ZakharovShabat
