import NLS.KdV.HillProductEquationRealDiagonal
import NLS.KdV.HillColumnDiagonalAsymptotic
import NLS.ZakharovShabat.SourcePsiQuotientMovingRows

/-! Each fixed numerator index has actual real period Jacobian
diagonal tending to one. All original low and collapsed entries remain
in the same full bounded operator. No uniformity in n is asserted here. -/
noncomputable section
open Set Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem sequenceJacobian_actual_real_diagonal_tendsto_one (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) (n : ℕ+) :
    Tendsto (fun j : ℕ => P.sequenceJacobian n (hillHminusPsiZeroDisplacement n ⟨q,hr⟩,q)
      (lp.single 2 ⟨j+1,by omega⟩ 1) ⟨j+1,by omega⟩) atTop (𝓝 1) := by
  let B := P.parent.parent.miuraBall.actionBall
  have hb := (P.parent.subset (P.subset hq)).1
  let u : PeriodOneRealL2 := ⟨B.lift q,B.lift_real q hb hr⟩
  let d := hillHminusPsiZeroDisplacement n ⟨q,hr⟩
  let D := fun m : ℕ+ => P.isolating.periodCircle (P.sourcePsi q) (P.image q hq).2 ((m:ℕ):ℤ)
    (P.centers ((m:ℕ):ℤ)) (P.radii ((m:ℕ):ℤ)) (P.radii_pos ((m:ℕ):ℤ)) (P.discs_eq ((m:ℕ):ℤ))
  have hmv (m : ℕ+) : ∃ μ ∈ sourcePeriodicSegment (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ),
      hillEnergyProductPeriodColumn n m (B.shift:ℂ) (P.sourcePsi q) (D m) d =
        -hillProductColumnGapNumerator n m (B.shift:ℂ) (P.sourcePsi q) ((m:ℕ):ℤ) d μ := by
    exact hillEnergyProductPeriodColumn_real_mean_value n m (B.shift:ℂ) (P.sourcePsi q)
      (hillMiuraRealSource u).property ((m:ℕ):ℤ) d (D m)
      (fun z hz => hillProductColumnGapNumerator_actual_real n m ⟨q,hr⟩ u B.shift
        (B.image q hb) (B.outside q hb) (D m) z hz)
  choose μ hμ hcol using hmv
  let z : ℕ → ℂ := fun j => μ ⟨j+1,by omega⟩
  have hz (j : ℕ) : z j ∈ P.discs ((j:ℤ)+1) := by
    have h := P.isolating.gap (P.sourcePsi q) (P.image q hq).2
      (((⟨j+1,by omega⟩:ℕ+):ℕ):ℤ) (hμ ⟨j+1,by omega⟩)
    simpa only [z,Nat.cast_add,Nat.cast_one] using h
  have hplace : ∀ k : ℤ, hillIndependentFrequency ((B.shift:ℂ),d) k ∈ P.discs k := by
    intro k
    exact P.isolating.gap (P.sourcePsi q) (P.image q hq).2 k
      (P.parent.actual_independentFrequency_mem_signed_gap n q (P.subset hq) hr k)
  have hquot := P.quotients.tendsto_quotient_positive_rows P.isolating P.V_open
    (P.sourcePsi q) (P.image q hq).1 (P.image q hq).2
    (hillIndependentFrequencyDisplacement ((B.shift:ℂ),d)) z hz
  have hlim := hillWeightedColumnGapNumerator_tendsto_of_quotient P.isolating (P.sourcePsi q)
    (P.image q hq).2 (B.shift:ℂ) d hplace n z hz hquot
  have ht := hlim.neg
  simp only [neg_neg] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (n:ℕ)] with j hj
  let m : ℕ+ := ⟨j+1,by omega⟩
  have hmn : m ≠ n := by intro he; have h := congrArg (fun k : ℕ+ => (k:ℕ)) he; change j+1 = (n:ℕ) at h; omega
  have hm : ((m:ℕ):ℤ) = (j:ℤ)+1 := by simp [m]
  rw [P.sequenceJacobian_coordinate n m m d q (P.actual_real_graph_mem q hq hr n) (D m) rfl rfl,if_neg hmn,hcol m]
  change -(hillPeriodEquationWeight n m*hillProductColumnGapNumerator n m (B.shift:ℂ)
    (P.sourcePsi q) ((j:ℤ)+1) d (z j)) =
    hillPeriodEquationWeight n m*(-hillProductColumnGapNumerator n m (B.shift:ℂ) (P.sourcePsi q) ((m:ℕ):ℤ) d (μ m))
  rw [hm]
  exact (mul_neg _ _).symm

end NLS.KdV.HillProductEquationPatch
