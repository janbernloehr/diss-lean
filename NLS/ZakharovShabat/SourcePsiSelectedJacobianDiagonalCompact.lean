import NLS.ZakharovShabat.SourcePsiSelectedJacobianEntry
import NLS.ZakharovShabat.SourcePsiJacobianUniformDiagonalTail
import NLS.ZakharovShabat.SourcePsiJacobianUniformOffDiagonalTail
import NLS.ZakharovShabat.SourcePsiJacobianAllGapNonzero
import NLS.SequenceSpaces.DeletedJacobianCompactRemainder
import NLS.SequenceSpaces.DeletedJacobianInvertibleDiagonal

/-!
# One selected psi Jacobian with diagonal and compact parts

The scalar diagonal and off-diagonal estimates hold on a common
free-centered tail of one locally selected contour family. They give
a separated diagonal tail and a compact off-diagonal remainder for
the same bounded Jacobian. Its remaining invertibility condition is
nonvanishing on finitely many retained rows.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- On one locally selected contour family, the bounded psi Jacobian
splits into its diagonal multiplier and a compact remainder. For
real-type, quarter-π localized root data, the diagonal is separated
from zero on a parameter-dependent tail. Nonvanishing on the finite
head makes that multiplier bijective. -/
theorem exists_local_sourcePsi_selectedJacobian_diagonalPlusCompact
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (n : ℤ) (a₀ : DeletedCoeff p n) :
    ∃ U : Set (DeletedCoeff p n × CoeffPair p), IsOpen U ∧
      (a₀,φ) ∈ U ∧
      ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
        ∃ Niso : ℕ, ∃ εiso : ℝ,
        (∀ t ∈ U, ∀ m : ℤ,
          sourceSpectralCluster hp hp1 t.2 m ⊆
            sourceIsolatingDisc hp hp1 φ Niso εiso m) ∧
        (∀ i j : ℤ, i ≠ j →
          Disjoint (sourceIsolatingDisc hp hp1 φ Niso εiso i)
            (sourceIsolatingDisc hp hp1 φ Niso εiso j)) ∧
        (∀ m : ℤ, closedBall (c m) (R m) ⊆
          sourceIsolatingDisc hp hp1 φ Niso εiso m) ∧
        ∀ a : DeletedCoeff p n, ∀ ψ : CoeffPair p,
          (a,ψ) ∈ U →
          IsRealType (CoeffPair.toMax p ψ) →
          (∀ j : ℤ, (displacedRoots (a : Coeff p) j).im = 0) →
          (∀ j : ℤ, ‖(a : Coeff p) j‖ ≤ Real.pi/4) →
          let Q : DeletedCoeff p n →L[ℂ] DeletedCoeff p n :=
            sourcePsiSelectedRootJacobian hp hp1 n c R a ψ
          let d : Coeff ⊤ := Coeff.deletedJacobianDiagonalSymbol n Q
          let D : DeletedCoeff p n →L[ℂ] DeletedCoeff p n :=
            Coeff.deletedMultiplierCLM n d
          let C : DeletedCoeff p n →L[ℂ] DeletedCoeff p n :=
            Coeff.deletedJacobianOffDiagonal n Q
          (∀ m : ℤ, closedBall (c m) (R m) ⊆
            sourceStandardRootOmittedDomain hp hp1 ψ m) ∧
          ∃ L : ℕ,
            (∀ m : ℤ, L ≤ m.natAbs → m ≠ n → 1 ≤ ‖d m‖) ∧
            IsCompactOperator C ∧
            ((∀ m : ℤ, m ≠ n → m.natAbs < L → d m ≠ 0) →
              Function.Bijective D) ∧
            (∀ m : ℤ, ∀ _hmn : m ≠ n,
              (∀ z ∈ sphere (c m) (R m),
                z ≠ displacedRoots (a : Coeff p) n) →
              AnalyticOnNhd ℂ
                (fun z => (((n-m : ℤ) : ℂ) *
                  sourcePsiGapRegularFactor hp hp1 n m (a : Coeff p) ψ z))
                (closedBall (c m) (R m)) →
              (∀ z ∈ standardRootGapSegment
                (sourceStandardRootMidpoint hp hp1 ψ m)
                (sourceStandardRootHalfGap hp hp1 ψ m),
                ∀ k : ℤ, k ≠ m →
                  z ≠ displacedRoots (a : Coeff p) k) →
              d m ≠ 0) ∧
            Q = D + C := by
  obtain ⟨Ueq,hUeqOpen,hbaseEq,Keq,c,R,hcReal,hchoice,hgeom,
      ⟨Niso,εiso,hcluster,hdisjoint,hfilled⟩,hmatrix⟩ :=
    exists_local_sourcePsi_selectedJacobian_matrixFormula
      hp hp1 φ hφ n a₀
  obtain ⟨Udiag,hUdiagOpen,hbaseDiag,Kdiag,Mdiag,hMdiag,hdiag⟩ :=
    exists_local_sourcePsi_diagonalJacobian_uniformTail
      hp hp1 φ hφ (a₀ : Coeff p)
  obtain ⟨Uoff,hUoffOpen,hbaseOff,Koff,Moff,hMoff,hoff⟩ :=
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
  refine ⟨U,hUopen,hbase,c,R,Niso,εiso,?_,hdisjoint,hfilled,?_⟩
  · intro t ht m
    exact hcluster t ht.1 m
  intro a ψ hpair hreal hroots hloc
  obtain ⟨Bdiag,hBdiagNorm,hBdiag⟩ :=
    hdiag n a ψ hpair.2.1 hreal hroots
  obtain ⟨Boff,hBoffNorm,hBoff⟩ :=
    hoff n a ψ hpair.2.2 hreal hroots hloc
  obtain ⟨L₀,hL₀⟩ :=
    exists_sourcePsi_diagonal_lp_tail_bound hp hp1 ψ Bdiag
  let Q : DeletedCoeff p n →L[ℂ] DeletedCoeff p n :=
    sourcePsiSelectedRootJacobian hp hp1 n c R a ψ
  let d : Coeff ⊤ := Coeff.deletedJacobianDiagonalSymbol n Q
  let D : DeletedCoeff p n →L[ℂ] DeletedCoeff p n :=
    Coeff.deletedMultiplierCLM n d
  let C : DeletedCoeff p n →L[ℂ] DeletedCoeff p n :=
    Coeff.deletedJacobianOffDiagonal n Q
  change (∀ m : ℤ, closedBall (c m) (R m) ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ m) ∧
    ∃ L : ℕ,
    (∀ m : ℤ, L ≤ m.natAbs → m ≠ n → 1 ≤ ‖d m‖) ∧
    IsCompactOperator C ∧
    ((∀ m : ℤ, m ≠ n → m.natAbs < L → d m ≠ 0) →
      Function.Bijective D) ∧
    (∀ m : ℤ, ∀ _hmn : m ≠ n,
      (∀ z ∈ sphere (c m) (R m),
        z ≠ displacedRoots (a : Coeff p) n) →
      AnalyticOnNhd ℂ
        (fun z => (((n-m : ℤ) : ℂ) *
          sourcePsiGapRegularFactor hp hp1 n m (a : Coeff p) ψ z))
        (closedBall (c m) (R m)) →
      (∀ z ∈ standardRootGapSegment
        (sourceStandardRootMidpoint hp hp1 ψ m)
        (sourceStandardRootHalfGap hp hp1 ψ m),
        ∀ k : ℤ, k ≠ m →
          z ≠ displacedRoots (a : Coeff p) k) →
      d m ≠ 0) ∧ Q = D + C
  have htail : ∀ m : ℤ, max K L₀ ≤ m.natAbs →
      m ≠ n → 1 ≤ ‖d m‖ := by
    intro m hm hmn
    have hmDiag : Kdiag ≤ m.natAbs := by dsimp [K] at hm; omega
    have hmL : L₀ ≤ m.natAbs := (le_max_right _ _).trans hm
    obtain ⟨hc,hR⟩ := hchoice m (by dsimp [K] at hm; omega)
    have hselected : ‖((Q (Coeff.deletedSingleCLM n m hmn 1) :
        DeletedCoeff p n) : Coeff p) m-2‖ ≤
          4*‖Bdiag m‖ +
            4*(‖sourcePeriodicMidpointDisplacement hp hp1 ψ m‖ +
              ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖/2) /
                ‖(Real.pi : ℂ)*((n-m : ℤ) : ℂ)‖ := by
      rw [hmatrix a ψ hpair.1 m m hmn]
      simpa only [hc,hR] using (hBdiag m hmDiag hmn).1
    have hsmall : ‖d m-2‖ < 1 := by
      rw [Coeff.deletedJacobianDiagonalSymbol_apply_other n m hmn]
      exact hselected.trans_lt ((hL₀ m hmL).2 n hmn)
    have htri : ‖(2 : ℂ)‖ ≤ ‖d m-2‖ + ‖d m‖ := by
      calc
        ‖(2 : ℂ)‖ = ‖((2 : ℂ)-d m)+d m‖ := by simp
        _ ≤ ‖(2 : ℂ)-d m‖ + ‖d m‖ := norm_add_le _ _
        _ = ‖d m-2‖ + ‖d m‖ := by rw [norm_sub_rev]
    have htwo : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [htwo] at htri
    linarith
  have hcompact : IsCompactOperator C := by
    let b : Coeff p :=
      sourcePsiOffDiagonalRowMajorant hp hp1 (a : Coeff p) ψ Boff
    let : Fact (1 ≤ p.conjExponent) :=
      ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩
    apply Coeff.isCompactOperator_deletedJacobianOffDiagonal_of_tailEntryBound
      p.conjExponent hp n Q b K
    intro m hm hmn k hkn hkm
    have hmOff : Koff ≤ m.natAbs := by dsimp [K] at hm; omega
    obtain ⟨hc,hR⟩ := hchoice m (by dsimp [K] at hm; omega)
    have hentry := hBoff m hmOff hmn k hkn (Ne.symm hkm)
    have hden : |(((m-k : ℤ) : ℝ))| = |(((k-m : ℤ) : ℝ))| := by
      simp only [Int.cast_sub]
      exact abs_sub_comm (m : ℝ) (k : ℝ)
    rw [hmatrix a ψ hpair.1 m k hkn]
    simpa only [b,Q,hc,hR,Complex.norm_intCast,hden] using hentry
  have hbij : (∀ m : ℤ, m ≠ n → m.natAbs < max K L₀ →
      d m ≠ 0) → Function.Bijective D := by
    intro hhead
    have hno : ∀ m : ℤ, m ≠ n → d m ≠ 0 := by
      intro m hmn
      by_cases hm : max K L₀ ≤ m.natAbs
      · have hb := htail m hm hmn
        intro hz
        rw [hz,norm_zero] at hb
        linarith
      · exact hhead m hmn (by omega)
    exact Coeff.deletedJacobianDiagonal_bijective_of_eventually_one_le
      n Q (max K L₀) hno (fun m hmn hm => htail m hm hmn)
  have hnonzero (m : ℤ) (hmn : m ≠ n)
      (havoidn : ∀ z ∈ sphere (c m) (R m),
        z ≠ displacedRoots (a : Coeff p) n)
      (hreg : AnalyticOnNhd ℂ
        (fun z => (((n-m : ℤ) : ℂ) *
          sourcePsiGapRegularFactor hp hp1 n m (a : Coeff p) ψ z))
        (closedBall (c m) (R m)))
      (hother : ∀ z ∈ standardRootGapSegment
        (sourceStandardRootMidpoint hp hp1 ψ m)
        (sourceStandardRootHalfGap hp hp1 ψ m),
        ∀ k : ℤ, k ≠ m →
          z ≠ displacedRoots (a : Coeff p) k) : d m ≠ 0 := by
    let x : ℝ := (c m).re
    have hx : (x : ℂ) = c m := by
      apply Complex.ext
      · rfl
      · simpa [x] using (hcReal m).symm
    obtain ⟨hR,hseg,hdom,hcircle⟩ := hgeom (a,ψ) hpair.1 m
    have hscalar := sourcePsi_diagonalJacobian_ne_zero_all_real_gaps
      hp hp1 ψ hreal n m hmn a hroots x (R m) hR
        (by simpa only [hx] using hseg)
        (by simpa only [hx] using hdom)
        (by simpa only [hx] using hcircle)
        (by simpa only [hx] using havoidn)
        (by simpa only [hx] using hreg) hother
    rw [Coeff.deletedJacobianDiagonalSymbol_apply_other n m hmn Q]
    change ((sourcePsiSelectedRootJacobian hp hp1 n c R a ψ
      (Coeff.deletedSingleCLM n m hmn 1) : DeletedCoeff p n) : Coeff p) m ≠ 0
    rw [hmatrix a ψ hpair.1 m m hmn]
    simpa only [hx] using hscalar
  have hdom (m : ℤ) : closedBall (c m) (R m) ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ m :=
    (hgeom (a,ψ) hpair.1 m).2.2.1
  exact ⟨hdom,max K L₀,htail,hcompact,hbij,hnonzero,
    Coeff.deletedJacobian_eq_diagonal_add_offDiagonal n Q⟩

end NLS.ZakharovShabat
