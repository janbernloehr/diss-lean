import NLS.ZakharovShabat.SourcePsiSelectedJacobianDiagonalEstimate
import NLS.SequenceSpaces.DeletedJacobianInvertibleDiagonal

/-!
# Uniformly separated diagonal tail of the selected psi Jacobian

The quantitative selected-operator estimate and decay of its `ℓᵖ`
error imply that the extracted diagonal symbol approaches two. For
each real-root parameter pair, its sufficiently distant retained
entries consequently have norm at least one.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Near a real-type source, the extracted diagonal of the selected
bounded Jacobian has a fixed lower bound on a parameter-dependent
tail. The initial contour cutoff and source neighborhood are shared;
the final cutoff may depend on the chosen `ℓᵖ` error sequence. -/
theorem exists_local_sourcePsi_selectedJacobian_diagonalSeparatedTail
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (n : ℤ) (a₀ : DeletedCoeff p n) :
    ∃ U : Set (DeletedCoeff p n × CoeffPair p), IsOpen U ∧
      (a₀,φ) ∈ U ∧
      ∃ K : ℕ, ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
        ∀ a : DeletedCoeff p n, ∀ ψ : CoeffPair p,
          (a,ψ) ∈ U →
          IsRealType (CoeffPair.toMax p ψ) →
          (∀ j : ℤ, (displacedRoots (a : Coeff p) j).im = 0) →
          ∃ L : ℕ, K ≤ L ∧
            ∀ m : ℤ, L ≤ m.natAbs → ∀ _hmn : m ≠ n,
              1 ≤ ‖Coeff.deletedJacobianDiagonalSymbol n
                (sourcePsiSelectedRootJacobian hp hp1 n c R a ψ) m‖ := by
  obtain ⟨U,hUopen,hbase,K,c,R,hchoice,M,hM,hestimate⟩ :=
    exists_local_sourcePsi_selectedJacobian_diagonalUniformEstimate
      hp hp1 φ hφ n a₀
  refine ⟨U,hUopen,hbase,K,c,R,?_⟩
  intro a ψ hpair hreal hroots
  obtain ⟨B,hBnorm,hB⟩ := hestimate a ψ hpair hreal hroots
  obtain ⟨L₀,hL₀⟩ := exists_sourcePsi_diagonal_lp_tail_bound hp hp1 ψ B
  refine ⟨max K L₀,le_max_left _ _,?_⟩
  intro m hm hmn
  have hmK : K ≤ m.natAbs := (le_max_left _ _).trans hm
  have hmL : L₀ ≤ m.natAbs := (le_max_right _ _).trans hm
  let Q : DeletedCoeff p n →L[ℂ] DeletedCoeff p n :=
    sourcePsiSelectedRootJacobian hp hp1 n c R a ψ
  let d : Coeff ⊤ := Coeff.deletedJacobianDiagonalSymbol n Q
  have hsmall : ‖d m-2‖ < 1 := by
    rw [Coeff.deletedJacobianDiagonalSymbol_apply_other n m hmn]
    exact ((hB m hmK hmn).1).trans_lt ((hL₀ m hmL).2 n hmn)
  have htri : ‖(2 : ℂ)‖ ≤ ‖d m-2‖ + ‖d m‖ := by
    calc
      ‖(2 : ℂ)‖ = ‖((2 : ℂ)-d m)+d m‖ := by simp
      _ ≤ ‖(2 : ℂ)-d m‖ + ‖d m‖ := norm_add_le _ _
      _ = ‖d m-2‖ + ‖d m‖ := by rw [norm_sub_rev]
  have htwo : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [htwo] at htri
  change 1 ≤ ‖d m‖
  linarith

/-- Once the finitely many remaining retained diagonal entries are
nonzero, the selected psi Jacobian's extracted diagonal multiplier is
an isomorphism of the deleted coefficient space. -/
theorem exists_local_sourcePsi_selectedJacobian_diagonalBijective_of_finiteHead
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (n : ℤ) (a₀ : DeletedCoeff p n) :
    ∃ U : Set (DeletedCoeff p n × CoeffPair p), IsOpen U ∧
      (a₀,φ) ∈ U ∧
      ∃ K : ℕ, ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
        ∀ a : DeletedCoeff p n, ∀ ψ : CoeffPair p,
          (a,ψ) ∈ U →
          IsRealType (CoeffPair.toMax p ψ) →
          (∀ j : ℤ, (displacedRoots (a : Coeff p) j).im = 0) →
          ∃ L : ℕ, K ≤ L ∧
            ((∀ m : ℤ, m ≠ n → m.natAbs < L →
              Coeff.deletedJacobianDiagonalSymbol n
                (sourcePsiSelectedRootJacobian hp hp1 n c R a ψ) m ≠ 0) →
              Function.Bijective
                (Coeff.deletedMultiplierCLM (p := p) n
                  (Coeff.deletedJacobianDiagonalSymbol n
                    (sourcePsiSelectedRootJacobian hp hp1 n c R a ψ)))) := by
  obtain ⟨U,hUopen,hbase,K,c,R,hsep⟩ :=
    exists_local_sourcePsi_selectedJacobian_diagonalSeparatedTail
      hp hp1 φ hφ n a₀
  refine ⟨U,hUopen,hbase,K,c,R,?_⟩
  intro a ψ hpair hreal hroots
  obtain ⟨L,hKL,htail⟩ := hsep a ψ hpair hreal hroots
  refine ⟨L,hKL,?_⟩
  intro hhead
  let Q : DeletedCoeff p n →L[ℂ] DeletedCoeff p n :=
    sourcePsiSelectedRootJacobian hp hp1 n c R a ψ
  have hno : ∀ m : ℤ, m ≠ n →
      Coeff.deletedJacobianDiagonalSymbol n Q m ≠ 0 := by
    intro m hmn
    by_cases hm : L ≤ m.natAbs
    · have hbound := htail m hm hmn
      change 1 ≤ ‖Coeff.deletedJacobianDiagonalSymbol n Q m‖ at hbound
      intro hz
      rw [hz, norm_zero] at hbound
      linarith
    · exact hhead m hmn (by omega)
  exact Coeff.deletedJacobianDiagonal_bijective_of_eventually_one_le
    n Q L hno (fun m hmn hm => htail m hm hmn)

end NLS.ZakharovShabat
