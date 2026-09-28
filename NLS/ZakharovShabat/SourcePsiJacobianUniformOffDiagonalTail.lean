import NLS.ZakharovShabat.SourcePsiJacobianOffDiagonalRowMajorant
import NLS.ZakharovShabat.SourcePsiGlobalHeadDiscBound
import NLS.ZakharovShabat.SourceNormalizedActionUniformTailCircles
import NLS.ZakharovShabat.SourcePsiNearFreeRegularAnalytic

/-!
# Locally uniform off-diagonal psi Jacobian tail

The selected contour family, quotient majorant, small source gaps,
and regular-factor analyticity hold on a common neighborhood of an
arbitrary real-type source. Bounds on distant input roots suffice for
the off-diagonal Jacobian estimate on every sufficiently distant
selected row, uniformly in the deleted index.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- One source/root neighborhood and selected-index cutoff give the
off-diagonal row estimate on distant input columns. The row majorant
is an actual `ℓᵖ` sequence with a locally bounded quotient correction. -/
theorem exists_local_sourcePsi_offDiagonalJacobian_uniformTail_tailColumns
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (a₀ : Coeff p) :
    ∃ U : Set (Coeff p × CoeffPair p), IsOpen U ∧
      (a₀,φ) ∈ U ∧
      ∃ K : ℕ, ∃ M : ℝ, 0 ≤ M ∧
        ∀ n : ℤ, ∀ a : DeletedCoeff p n, ∀ ψ : CoeffPair p,
          ((a : Coeff p),ψ) ∈ U →
          IsRealType (CoeffPair.toMax p ψ) →
          (∀ j : ℤ, (displacedRoots (a : Coeff p) j).im = 0) →
          ∀ Kcol : ℕ,
          (∀ j : ℤ, Kcol ≤ j.natAbs →
            ‖(a : Coeff p) j‖ ≤ Real.pi/4) →
          ∃ B : Coeff p, ‖B‖ ≤ M ∧
            ∀ m : ℤ, K ≤ m.natAbs → ∀ _hmn : m ≠ n,
              ∀ k : ℤ, Kcol ≤ k.natAbs →
                ∀ hkn : k ≠ n, ∀ _hmk : m ≠ k,
                ‖deriv (fun t : ℂ =>
                  sourcePsiDeletedEquationCoordinate hp hp1 n m
                    (a+Coeff.deletedSingleCLM n k hkn t) ψ
                    ((Real.pi : ℂ)*m) (Real.pi/8)) 0‖ ≤
                  ‖sourcePsiOffDiagonalRowMajorant hp hp1
                    (a : Coeff p) ψ B m‖ /
                    ‖((m-k : ℤ) : ℂ)‖ := by
  obtain ⟨Ureg,hUregOpen,hbaseReg,Kreg,c,R,_,hchoice,hgeom,_,
    M,hM,hmajor⟩ :=
    exists_local_sourcePsiQuotient_uniformAllSelectedDiscMajorant
      hp hp1 φ hφ a₀
  obtain ⟨Ksmall,Vsmall,hVsmallOpen,hφVsmall,hsmall⟩ :=
    exists_local_sourcePeriodicMidpointGap_tiny_tail hp hp1 φ
  obtain ⟨W,hWopen,_,hrealW,hQanalytic⟩ :=
    exists_global_source_analytic_singleRootQuotient hp hp1
  let V : Set (CoeffPair p) := Vsmall ∩ W
  let U : Set (Coeff p × CoeffPair p) := Ureg ∩ (Set.univ ×ˢ V)
  have hUopen : IsOpen U :=
    hUregOpen.inter (isOpen_univ.prod (hVsmallOpen.inter hWopen))
  have hbase : (a₀,φ) ∈ U :=
    ⟨hbaseReg,Set.mem_univ _,⟨hφVsmall,hrealW hφ⟩⟩
  let K : ℕ := max (Kreg+1) Ksmall
  refine ⟨U,hUopen,hbase,K,M,hM,?_⟩
  intro n a ψ hpair hreal hroots Kcol hlocalized
  obtain ⟨B,hBnorm,hB⟩ := hmajor ((a : Coeff p),ψ) hpair.1
  refine ⟨B,hBnorm,?_⟩
  intro m hm hmn k hkcol hkn hmk
  have hmReg : Kreg < m.natAbs := by dsimp [K] at hm; omega
  have hmSmall : Ksmall ≤ m.natAbs := by dsimp [K] at hm; omega
  obtain ⟨hc,hR⟩ := hchoice m hmReg
  have hgeomM := hgeom ((a : Coeff p),ψ) hpair.1 m
  have hseg : sourcePeriodicSegment hp hp1 ψ m ⊆
      ball ((Real.pi : ℂ)*m) (Real.pi/8) := by
    simpa only [hc,hR] using hgeomM.2.1
  have hdom : closedBall ((Real.pi : ℂ)*m) (Real.pi/8) ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ m := by
    simpa only [hc,hR] using hgeomM.2.2.1
  have hcircle : sphere ((Real.pi : ℂ)*m) (Real.pi/8) ⊆
      sourceCanonicalRootDomain hp hp1 ψ := by
    simpa only [hc,hR] using hgeomM.2.2.2
  have hψsmall : ψ ∈ Vsmall := hpair.2.2.1
  have hψW : ψ ∈ W := hpair.2.2.2
  obtain ⟨hmidSmall,hgapSmall⟩ := hsmall ψ hψsmall m hmSmall
  have hmidCoeff :
      ‖sourcePeriodicMidpointDisplacement hp hp1 ψ m‖ ≤
        Real.pi/64 := by
    simpa only [sourcePeriodicMidpointDisplacement_apply,
      sourceStandardRootMidpoint] using hmidSmall
  have hsmallQuarter :
      ‖sourcePeriodicMidpointDisplacement hp hp1 ψ m‖ +
        ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖/2 ≤
          Real.pi/4 := by
    nlinarith [Real.pi_pos]
  have hQdisc : ∀ z ∈ closedBall ((Real.pi : ℂ)*m) (Real.pi/8),
      ‖sourceSingleRootQuotientJointProduct hp hp1 m
        (z,((a : Coeff p),ψ))-1‖ ≤ ‖B m‖ := by
    intro z hz
    have hz' : z ∈ closedBall (c m) (R m) := by
      simpa only [hc,hR] using hz
    exact hB m z hz'
  have hreg : AnalyticOnNhd ℂ
      (fun z => (((n-m : ℤ) : ℂ) *
        sourcePsiGapRegularFactor hp hp1 n m (a : Coeff p) ψ z))
      (closedBall ((Real.pi : ℂ)*m) (Real.pi/8)) :=
    analyticOnNhd_deletedPsi_gapRegularFactor_of_omitted_disc
      hp hp1 n m (Ne.symm hmn) a ψ W hψW (hQanalytic m).2
        (Real.pi/8) (by nlinarith [Real.pi_pos]) hdom
  have havoidn : ∀ z ∈ sphere ((Real.pi : ℂ)*m) (Real.pi/8),
      z ≠ displacedRoots (a : Coeff p) n := by
    intro z hz
    have ha : (a : Coeff p) n = 0 := a.property
    rw [show displacedRoots (a : Coeff p) n =
      (Real.pi : ℂ)*n by simp [displacedRoots,ha]]
    exact freeCircle_point_ne_freeCenter m n (Real.pi/8)
      (by positivity) (by nlinarith [Real.pi_pos]) z hz
  exact norm_sourcePsi_offDiagonalJacobian_le_rowMajorant
    hp hp1 ψ hreal n m k hmn hkn hmk a hroots
      (Real.pi/8) (by positivity) (by nlinarith [Real.pi_pos])
      hseg hdom hcircle havoidn hreg B (hlocalized k hkcol)
      hsmallQuarter hQdisc

/-- The all-column form of the off-diagonal tail estimate follows by
taking the column cutoff to be zero. -/
theorem exists_local_sourcePsi_offDiagonalJacobian_uniformTail
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (a₀ : Coeff p) :
    ∃ U : Set (Coeff p × CoeffPair p), IsOpen U ∧
      (a₀,φ) ∈ U ∧
      ∃ K : ℕ, ∃ M : ℝ, 0 ≤ M ∧
        ∀ n : ℤ, ∀ a : DeletedCoeff p n, ∀ ψ : CoeffPair p,
          ((a : Coeff p),ψ) ∈ U →
          IsRealType (CoeffPair.toMax p ψ) →
          (∀ j : ℤ, (displacedRoots (a : Coeff p) j).im = 0) →
          (∀ j : ℤ, ‖(a : Coeff p) j‖ ≤ Real.pi/4) →
          ∃ B : Coeff p, ‖B‖ ≤ M ∧
            ∀ m : ℤ, K ≤ m.natAbs → ∀ _hmn : m ≠ n,
              ∀ k : ℤ, ∀ hkn : k ≠ n, ∀ _hmk : m ≠ k,
                ‖deriv (fun t : ℂ =>
                  sourcePsiDeletedEquationCoordinate hp hp1 n m
                    (a+Coeff.deletedSingleCLM n k hkn t) ψ
                    ((Real.pi : ℂ)*m) (Real.pi/8)) 0‖ ≤
                  ‖sourcePsiOffDiagonalRowMajorant hp hp1
                    (a : Coeff p) ψ B m‖ /
                    ‖((m-k : ℤ) : ℂ)‖ := by
  obtain ⟨U,hUopen,hbase,K,M,hM,htail⟩ :=
    exists_local_sourcePsi_offDiagonalJacobian_uniformTail_tailColumns
      hp hp1 φ hφ a₀
  refine ⟨U,hUopen,hbase,K,M,hM,?_⟩
  intro n a ψ hpair hreal hroots hloc
  obtain ⟨B,hBnorm,hB⟩ :=
    htail n a ψ hpair hreal hroots 0 (fun j _ => hloc j)
  refine ⟨B,hBnorm,?_⟩
  intro m hm hmn k hkn hmk
  exact hB m hm hmn k (Nat.zero_le _) hkn hmk

end NLS.ZakharovShabat
