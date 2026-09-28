import NLS.ZakharovShabat.SourcePsiJacobianUniformOffDiagonalTail
import NLS.ZakharovShabat.SourcePsiJacobianDiagonalTail

/-!
# Locally uniform diagonal psi Jacobian tail

The selected contour family, quotient majorant, small spectral gaps,
and regular-factor analyticity also assemble for the diagonal entry.
The source neighborhood and initial selected-row cutoff are common to
all deleted indices. For each parameter pair, the resulting `ℓᵖ`
majorant gives a further cutoff where every diagonal entry is nonzero.
-/

noncomputable section
set_option maxHeartbeats 800000
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- On one neighborhood of arbitrary real-type source data, every
distant selected diagonal entry has the all-gap `2 + error` estimate.
The quotient correction is an `ℓᵖ` sequence with locally bounded norm. -/
theorem exists_local_sourcePsi_diagonalJacobian_uniformTail
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
          ∃ B : Coeff p, ‖B‖ ≤ M ∧
            ∀ m : ℤ, K ≤ m.natAbs → ∀ _hmn : m ≠ n,
              ‖deriv (fun t : ℂ =>
                sourcePsiDeletedEquationCoordinate hp hp1 n m
                  (a+Coeff.deletedSingleCLM n m _hmn t) ψ
                  ((Real.pi : ℂ)*m) (Real.pi/8)) 0-2‖ ≤
                4*‖B m‖ +
                  4*(‖sourcePeriodicMidpointDisplacement hp hp1 ψ m‖ +
                    ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖/2) /
                      ‖(Real.pi : ℂ)*((n-m : ℤ) : ℂ)‖ := by
  obtain ⟨Ureg,hUregOpen,hbaseReg,Kreg,c,R,_,hchoice,hgeom,
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
  intro n a ψ hpair hreal hroots
  obtain ⟨B,hBnorm,hB⟩ := hmajor ((a : Coeff p),ψ) hpair.1
  refine ⟨B,hBnorm,?_⟩
  intro m hm hmn
  have hmReg : Kreg < m.natAbs := by dsimp [K] at hm; omega
  have hmSmall : Ksmall ≤ m.natAbs := by dsimp [K] at hm; omega
  have hcenter : ((Real.pi*(m:ℝ) : ℝ) : ℂ) =
      (Real.pi : ℂ)*m := by push_cast; rfl
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
  have hsmallDenom :
      2*(‖sourcePeriodicMidpointDisplacement hp hp1 ψ m‖ +
        ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖/2) ≤ Real.pi := by
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
  have hbound := norm_sourcePsi_diagonalJacobian_sub_two_le_all_real_gaps
    hp hp1 ψ hreal n m hmn a hroots
      (Real.pi*(m:ℝ)) (Real.pi/8) (by positivity)
      (by simpa only [hcenter] using hseg)
      (by simpa only [hcenter] using hdom)
      (by simpa only [hcenter] using hcircle)
      (by simpa only [hcenter] using havoidn)
      (by simpa only [hcenter] using hreg)
      B hsmallDenom (by simpa only [hcenter] using hQdisc)
  simpa only [hcenter] using hbound

/-- For each real-root parameter pair in that neighborhood,
one further two-sided cutoff makes every diagonal entry nonzero,
uniformly in the deleted index. -/
theorem exists_local_sourcePsi_diagonalJacobian_nonzeroTail
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (a₀ : Coeff p) :
    ∃ U : Set (Coeff p × CoeffPair p), IsOpen U ∧
      (a₀,φ) ∈ U ∧ ∃ K : ℕ,
        ∀ n : ℤ, ∀ a : DeletedCoeff p n, ∀ ψ : CoeffPair p,
          ((a : Coeff p),ψ) ∈ U →
          IsRealType (CoeffPair.toMax p ψ) →
          (∀ j : ℤ, (displacedRoots (a : Coeff p) j).im = 0) →
          ∃ L : ℕ, K ≤ L ∧
            ∀ m : ℤ, L ≤ m.natAbs → ∀ hmn : m ≠ n,
              deriv (fun t : ℂ =>
                sourcePsiDeletedEquationCoordinate hp hp1 n m
                  (a+Coeff.deletedSingleCLM n m hmn t) ψ
                  ((Real.pi : ℂ)*m) (Real.pi/8)) 0 ≠ 0 := by
  obtain ⟨U,hUopen,hbase,K,M,hM,hbound⟩ :=
    exists_local_sourcePsi_diagonalJacobian_uniformTail
      hp hp1 φ hφ a₀
  refine ⟨U,hUopen,hbase,K,?_⟩
  intro n a ψ hpair hreal hroots
  obtain ⟨B,_,hB⟩ := hbound n a ψ hpair hreal hroots
  obtain ⟨L₀,hL₀⟩ :=
    exists_sourcePsi_diagonal_lp_tail_bound hp hp1 ψ B
  refine ⟨max K L₀,le_max_left _ _,?_⟩
  intro m hm hmn hzero
  have hK : K ≤ m.natAbs := (le_max_left _ _).trans hm
  have hLbound : L₀ ≤ m.natAbs := (le_max_right _ _).trans hm
  have herr := (hB m hK hmn).trans_lt ((hL₀ m hLbound).2 n hmn)
  rw [hzero] at herr
  norm_num at herr

end NLS.ZakharovShabat
