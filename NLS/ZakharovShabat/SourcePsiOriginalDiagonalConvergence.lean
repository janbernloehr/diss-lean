import NLS.ZakharovShabat.SourcePsiOriginalDiagonalDifference
import NLS.SequenceSpaces.ReciprocalColumnHeadTail

/-!
# Explicit diagonal convergence on the original real domain

The p-th power norm splits exactly at the moving omitted coordinate.
One lp sequence controls that coordinate, and the retained diagonal has
a quantitative reciprocal head plus output-tail bound. The midpoint and
gap tails are taken in the output index, so they vanish for finite p.
The diagonal multipliers converge in operator norm in both directions.
-/

noncomputable section
open Set Complex Metric Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The diagonal norm difference splits exactly into the moving omitted
coordinate and the retained coordinates, with no multiplicative loss. -/
theorem sourcePsiOriginal_diagonalDifference_norm_rpow
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (a : Coeff p) (φ : CoeffPair p) (h : Coeff p) :
    ‖(Coeff.multiplierCLM (p := p) (Coeff.operatorDiagonalSymbol
        (sourcePsiOriginalLimitOperator hp hp1 a φ)) -
      Coeff.multiplierCLM (p := p) (Coeff.operatorDiagonalSymbol
        (sourcePsiOriginalFullRootJacobian hp hp1 n a φ))) h‖ ^ p.toReal =
      ‖((sourcePsiOriginalLimitOperator hp hp1 a φ (lp.single p n 1)) n-2)*h n‖ ^ p.toReal +
      ∑' m : ℤ, if m = n then 0 else
        ‖((sourcePsiOriginalLimitOperator hp hp1 a φ (lp.single p m 1)) m-
          sourcePsiOriginalJacobianEntry hp hp1 n m m a φ)*h m‖ ^ p.toReal := by
  classical
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos (zero_lt_one.trans hp1).ne' hp
  let b : Coeff p := (Coeff.multiplierCLM (p := p) (Coeff.operatorDiagonalSymbol
      (sourcePsiOriginalLimitOperator hp hp1 a φ)) -
    Coeff.multiplierCLM (p := p) (Coeff.operatorDiagonalSymbol
      (sourcePsiOriginalFullRootJacobian hp hp1 n a φ))) h
  have hb (m : ℤ) : b m =
      ((sourcePsiOriginalLimitOperator hp hp1 a φ (lp.single p m 1)) m-
       (sourcePsiOriginalFullRootJacobian hp hp1 n a φ (lp.single p m 1)) m)*h m := by
    simp only [b,sub_apply,lp.coeFn_sub,Pi.sub_apply,
      Coeff.multiplierCLM_apply,Coeff.multiplier_apply,Coeff.operatorDiagonalSymbol_apply]
    ring
  change ‖b‖ ^ p.toReal = _
  rw [lp.norm_rpow_eq_tsum hp0,((lp.memℓp b).summable hp0).tsum_eq_add_tsum_ite n]
  congr 1
  · rw [hb]
    simp [sourcePsiOriginalFullRootJacobian,Coeff.deletedJacobianExtension]
  · apply tsum_congr
    intro m
    split_ifs with hmn
    · rfl
    · rw [hb,sourcePsiOriginalFullRootJacobian_entry hp hp1 n m m hmn]

/-- One actual lp sequence controls the distinguished diagonal term
for every input vector, retaining the constant one. -/
theorem SourceLemma12_4Data.originalLimitOperator_movingDiagonal_bound
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (H : SourceLemma12_4Data hp hp1 W) (hW : IsOpen W)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c) (hV : IsOpen V)
    (φ : CoeffPair p) (hφW : φ ∈ W) (hφV : φ ∈ V)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (a : Coeff p) (ha : a ∈ sourcePsiOriginalRootPlacement D)
    (haReal : ∀ k : ℤ, (a k).im = 0) :
    ∃ S : Coeff p, ∀ n : ℤ, ∀ h : Coeff p,
      ‖((sourcePsiOriginalLimitOperator hp hp1 a φ (lp.single p n 1)) n-2)*h n‖ ≤
        ‖S n‖*‖h‖ := by
  obtain ⟨U,_,hbase,_,C,_,hb⟩ :=
    H.originalLimitOperator_diagonal_lp hW hD hV φ hφW hφV a
  obtain ⟨S,_,hS⟩ := hb (a,φ) hbase hφ ha haReal
  refine ⟨S,?_⟩
  intro n h
  rw [hS n,add_sub_cancel_left,norm_mul]
  exact mul_le_mul_of_nonneg_left
    (lp.norm_apply_le_norm (zero_lt_one.trans hp1).ne' h n) (norm_nonneg _)

/-- The original diagonal multipliers converge in operator norm at
every real placed root input, in both index directions. -/
theorem SourceLemma12_4Data.originalFullRootJacobian_diagonal_tendsto
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (H : SourceLemma12_4Data hp hp1 W)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (φ : CoeffPair p) (hφW : φ ∈ W) (hφV : φ ∈ V)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (a : Coeff p) (ha : a ∈ sourcePsiOriginalRootPlacement D)
    (haReal : ∀ k : ℤ, (a k).im = 0) :
    Tendsto (fun n : ℤ => Coeff.multiplierCLM (p := p)
      (Coeff.operatorDiagonalSymbol (sourcePsiOriginalFullRootJacobian hp hp1 n a φ)))
      (Filter.comap Int.natAbs atTop)
      (𝓝 (Coeff.multiplierCLM (p := p)
        (Coeff.operatorDiagonalSymbol (sourcePsiOriginalLimitOperator hp hp1 a φ)))) := by
  let l : Filter ℤ := Filter.comap Int.natAbs atTop
  let : NeBot l := (inferInstance : NeBot (atTop : Filter ℕ)).comap_of_surj Int.natAbs_surjective
  exact Coeff.tendsto_operatorDiagonalMultiplier_of_uniform_constantTail l
    (fun n => sourcePsiOriginalFullRootJacobian hp hp1 n a φ)
    (sourcePsiOriginalLimitOperator hp hp1 a φ) 2
    (fun m => H.originalLimitOperator_spec hD φ hφW hφV hφ a ha (lp.single p m 1) m)
    (H.originalFullRootJacobian_diagonal_uniformTail φ hφW hφ a haReal)

end NLS.ZakharovShabat

noncomputable section
open Set Complex Metric Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual diagonal operator difference is controlled by its moving
diagonal correction, the omitted root displacement, a reciprocal head,
and the two actual lp tails. Every constant precedes both integer indices. -/
theorem SourceLemma12_4Data.originalFullRootJacobian_diagonal_head_tail
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (H : SourceLemma12_4Data hp hp1 W) (hW : IsOpen W)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c) (hV : IsOpen V)
    (φ : CoeffPair p) (hφW : φ ∈ W) (hφV : φ ∈ V)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (a : Coeff p) (ha : a ∈ sourcePsiOriginalRootPlacement D)
    (haReal : ∀ k : ℤ, (a k).im = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ S : Coeff p,
      (∀ m : ℤ, (sourcePsiOriginalLimitOperator hp hp1 a φ (lp.single p m 1)) m = 2+S m) ∧
      ∀ n : ℤ, n ≠ 0 → ∀ K : ℕ, 2*K ≤ n.natAbs →
        ‖Coeff.multiplierCLM (p := p) (Coeff.operatorDiagonalSymbol
            (sourcePsiOriginalFullRootJacobian hp hp1 n a φ)) -
          Coeff.multiplierCLM (p := p) (Coeff.operatorDiagonalSymbol
            (sourcePsiOriginalLimitOperator hp hp1 a φ))‖ ≤
        ‖S n‖+C*(‖a n‖+
          (2/(n.natAbs:ℝ))*(‖sourcePeriodicMidpointDisplacement hp hp1 φ‖+
            ‖sourcePeriodicGapDisplacement hp hp1 φ‖)+
          ‖sourcePeriodicMidpointDisplacement hp hp1 φ-
            Coeff.truncate (Finset.Icc (-(K:ℤ)) (K:ℤ)) (sourcePeriodicMidpointDisplacement hp hp1 φ)‖+
          ‖sourcePeriodicGapDisplacement hp hp1 φ-
            Coeff.truncate (Finset.Icc (-(K:ℤ)) (K:ℤ)) (sourcePeriodicGapDisplacement hp hp1 φ)‖) := by
  obtain ⟨U,_,hbase,_,C,hC,hb⟩ :=
    H.originalJacobian_diagonalDifference_locally_bounded hW hD hV φ hφW hφV a
  obtain ⟨Us,_,hbaseS,_,Cs,_,hbs⟩ := H.originalLimitOperator_diagonal_lp hW hD hV φ hφW hφV a
  obtain ⟨S,_,hS⟩ := hbs (a,φ) hbaseS hφ ha haReal
  refine ⟨C,hC,S,hS,?_⟩
  intro n hn K hK
  let M := sourcePeriodicMidpointDisplacement hp hp1 φ
  let G := sourcePeriodicGapDisplacement hp hp1 φ
  let s : Finset ℤ := Finset.Icc (-(K:ℤ)) (K:ℤ)
  let B : ℝ := ‖S n‖+C*(‖a n‖+(2/(n.natAbs:ℝ))*(‖M‖+‖G‖)+
    ‖M-Coeff.truncate s M‖+‖G-Coeff.truncate s G‖)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  apply (Coeff.norm_multiplierCLM_sub_le (p := p) _ _).trans
  apply lp.norm_le_of_forall_le hB
  intro m
  change ‖(sourcePsiOriginalFullRootJacobian hp hp1 n a φ (lp.single p m 1)) m-
    (sourcePsiOriginalLimitOperator hp hp1 a φ (lp.single p m 1)) m‖ ≤ B
  by_cases hmn : m = n
  · subst m
    rw [hS n]
    have htwo : (sourcePsiOriginalFullRootJacobian hp hp1 n a φ (lp.single p n 1)) n = 2 := by
      simp [sourcePsiOriginalFullRootJacobian,Coeff.deletedJacobianExtension]
    rw [htwo,show (2:ℂ)-(2+S n) = -S n by ring,norm_neg]
    exact le_add_of_nonneg_right (by positivity)
  · rw [sourcePsiOriginalFullRootJacobian_entry hp hp1 n m m hmn]
    have hden : ‖((n-m:ℤ):ℂ)‖ = ((n-m).natAbs:ℝ) := by
      rw [Complex.norm_intCast,← Int.cast_abs,← Int.natCast_natAbs]
      simp
    have hd : (1:ℝ) ≤ ((n-m).natAbs:ℝ) := by
      exact_mod_cast (show 1 ≤ (n-m).natAbs from Int.natAbs_pos.mpr (sub_ne_zero.mpr (Ne.symm hmn)))
    have ha' : ‖a n‖/((n-m).natAbs:ℝ) ≤ ‖a n‖ := div_le_self (norm_nonneg _) hd
    have hM := Coeff.reciprocalEntry_le_head_tail n hn K hK M m hmn
    have hG := Coeff.reciprocalEntry_le_head_tail n hn K hK G m hmn
    have he := hb (a,φ) hbase hφ ha n m hmn
    rw [hden] at he
    apply he.trans
    change C*(‖a n‖+‖M m‖+‖G m‖)/((n-m).natAbs:ℝ) ≤ B
    calc
      _ = C*(‖a n‖/((n-m).natAbs:ℝ)+‖M m‖/((n-m).natAbs:ℝ)+‖G m‖/((n-m).natAbs:ℝ)) := by ring
      _ ≤ C*(‖a n‖+((2/(n.natAbs:ℝ))*‖M‖+‖M-Coeff.truncate s M‖)+
          ((2/(n.natAbs:ℝ))*‖G‖+‖G-Coeff.truncate s G‖)) :=
        mul_le_mul_of_nonneg_left (add_le_add (add_le_add ha' hM) hG) hC
      _ ≤ B := by dsimp only [B]; nlinarith [norm_nonneg (S n)]

end NLS.ZakharovShabat
