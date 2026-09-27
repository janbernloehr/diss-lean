import NLS.ZakharovShabat.SourcePsiGlobalDistantDeletedRegularFactor
import NLS.ZakharovShabat.SourcePsiNearFreeComplexUniformEquation

/-!
# Uniform psi equation bounds on the global free-centered tail

For a real-type base source, sufficiently distant selected gaps have
the same small complex geometry as the near-free case. The global
regular-factor majorant therefore gives a psi coordinate bound with
one constant independent of both spectral indices.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- On one neighborhood of an arbitrary real-type source and root
input, every sufficiently distant selected psi coordinate is bounded
by the three `ℓᵖ` displacement magnitudes, uniformly in the deleted
index once that index is also sufficiently distant. -/
theorem exists_local_sourcePsi_distantDeleted_tailCoordinateBound
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (a₀ : Coeff p) :
    ∃ U : Set (Coeff p × CoeffPair p), IsOpen U ∧
      (a₀,φ) ∈ U ∧
      ∃ N K : ℕ, ∃ C : ℝ, 0 ≤ C ∧
        ∀ n : ℤ, N ≤ n.natAbs →
          ∀ a : DeletedCoeff p n, ∀ ψ : CoeffPair p,
            ((a : Coeff p),ψ) ∈ U →
              ∀ m : ℤ, K ≤ m.natAbs →
                ‖(2*(Real.pi:ℂ))⁻¹ *
                  sourcePsiEquationCoordinate hp hp1 n m
                    (a : Coeff p) ψ ((Real.pi : ℂ)*m) (Real.pi/8)‖ ≤
                  C*(‖(a : Coeff p) m‖+
                    ‖sourcePeriodicMidpointDisplacement hp hp1 ψ m‖+
                    ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖) := by
  obtain ⟨Ureg,hUregOpen,hbaseReg,N,Kreg,c,R,hchoice,hgeom,M,hM,hreg⟩ :=
    exists_local_sourcePsi_distantDeleted_uniformRegularFactorMajorant
      hp hp1 φ hφ a₀
  obtain ⟨Ksmall,Vsmall,hVsmallOpen,hφVsmall,hsmall⟩ :=
    exists_local_sourcePeriodicMidpointGap_tiny_tail hp hp1 φ
  obtain ⟨Kgeom,Vgeom,hVgeomOpen,hφVgeom,hgeomTail⟩ :=
    exists_local_sourceNormalizedAction_uniform_tail_circle_data
      hp hp1 φ hφ
  obtain ⟨W,hWopen,_,hrealW,hQ⟩ :=
    exists_global_source_analytic_singleRootQuotient hp hp1
  have hφW : φ ∈ W := hrealW hφ
  let V : Set (CoeffPair p) := Vsmall ∩ Vgeom ∩ W
  have hVopen : IsOpen V :=
    (hVsmallOpen.inter hVgeomOpen).inter hWopen
  have hφV : φ ∈ V := ⟨⟨hφVsmall,hφVgeom⟩,hφW⟩
  let U : Set (Coeff p × CoeffPair p) :=
    Ureg ∩ (ball a₀ 1 ×ˢ V)
  have hUopen : IsOpen U := hUregOpen.inter (isOpen_ball.prod hVopen)
  have hbase : (a₀,φ) ∈ U :=
    ⟨hbaseReg,mem_ball_self (by norm_num),hφV⟩
  let K : ℕ := max (Kreg+1) (max Ksmall Kgeom)
  let T : ℝ := ‖a₀‖+1
  let J : ℝ := (Real.pi/8)*(T+Real.pi/8)*(Real.pi/32) /
    (2*(Real.pi/16)^3)
  let C : ℝ := (1+J)*((2/Real.pi)*(1+M))
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨U,hUopen,hbase,N,K,C,hC,?_⟩
  intro n hn a ψ hpair m hm
  obtain ⟨hpairReg,haBall,⟨⟨hψsmall,hψgeom⟩,hψW⟩⟩ := hpair
  obtain ⟨B,hBnorm,hB⟩ := hreg n hn a ψ hpairReg
  have hmReg : Kreg < m.natAbs := by dsimp [K] at hm; omega
  have hmSmall : Ksmall ≤ m.natAbs := by dsimp [K] at hm; omega
  have hmGeom : Kgeom ≤ m.natAbs := by dsimp [K] at hm; omega
  obtain ⟨hc,hR⟩ := hchoice m hmReg
  have ha : ‖(a : Coeff p)‖ ≤ T := by
    have hdist : ‖(a : Coeff p)-a₀‖ < 1 := by
      simpa only [mem_ball,dist_eq_norm] using haBall
    have hsum : ‖(a : Coeff p)‖ ≤ ‖a₀‖+‖(a : Coeff p)-a₀‖ := by
      have heq : (a : Coeff p) = a₀+((a : Coeff p)-a₀) := by abel
      calc
        ‖(a : Coeff p)‖ = ‖a₀+((a : Coeff p)-a₀)‖ :=
          congrArg norm heq
        _ ≤ _ := norm_add_le _ _
    dsimp [T]
    linarith
  by_cases hmn : m = n
  · subst m
    simp [sourcePsiEquationCoordinate]
    positivity
  have hacoord : ‖(a : Coeff p) m‖ ≤ T :=
    (lp.norm_apply_le_norm
      (ne_of_gt (zero_lt_one.trans_le Fact.out)) (a : Coeff p) m).trans ha
  have hdata := hgeomTail ψ hψgeom m hmGeom
  have hdom : closedBall ((Real.pi : ℂ)*m) (Real.pi/8) ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ m := hdata.2.1
  have hcircle : sphere ((Real.pi : ℂ)*m) (Real.pi/8) ⊆
      sourceCanonicalRootDomain hp hp1 ψ := by
    simpa only [hc,hR] using
      (hgeom ((a : Coeff p),ψ) hpairReg m).2.2.2
  have hBfree : ∀ z ∈ closedBall ((Real.pi : ℂ)*m) (Real.pi/8),
      ‖(((n-m : ℤ) : ℂ) *
        sourcePsiGapRegularFactor hp hp1 n m
          (a : Coeff p) ψ z)‖ ≤
        (2/Real.pi)*(1+‖B m‖) := by
    intro z hz
    have hz' : z ∈ closedBall (c m) (R m) := by
      simpa only [hc,hR] using hz
    exact hB m hmn z hz'
  have hcoord :=
    nearFree_complex_deletedPsi_normalizedCoordinate_bound_uniform
      hp hp1 ψ n m hmn a W hψW (hQ m).2
        hdom hcircle (hsmall ψ hψsmall m hmSmall).1
        (hsmall ψ hψsmall m hmSmall).2
        B hBfree T hacoord
  have hBcoord : ‖B m‖ ≤ M :=
    (lp.norm_apply_le_norm
      (ne_of_gt (zero_lt_one.trans_le Fact.out)) B m).trans hBnorm
  calc
    ‖(2*(Real.pi:ℂ))⁻¹ *
        sourcePsiEquationCoordinate hp hp1 n m (a : Coeff p) ψ
          ((Real.pi : ℂ)*m) (Real.pi/8)‖ ≤
      (1+J)*
        (‖(a : Coeff p) m‖+
          ‖sourcePeriodicMidpointDisplacement hp hp1 ψ m‖+
          ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖)*
          ((2/Real.pi)*(1+‖B m‖)) := hcoord
    _ ≤ (1+J)*
        (‖(a : Coeff p) m‖+
          ‖sourcePeriodicMidpointDisplacement hp hp1 ψ m‖+
          ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖)*
          ((2/Real.pi)*(1+M)) := by
            gcongr
    _ = _ := by dsimp [C]; ring

end NLS.ZakharovShabat
