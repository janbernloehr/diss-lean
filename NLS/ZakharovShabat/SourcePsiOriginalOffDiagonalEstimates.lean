import NLS.ZakharovShabat.SourcePsiOriginalOffDiagonalSplit
import NLS.ZakharovShabat.SourcePsiOriginalOffDiagonalDifference
import NLS.SequenceSpaces.DoubleReciprocalHeadTail

/-!
# Quantitative original off-diagonal norm estimates

Holder controls the distinguished row; the actual column and retained
operator have explicit finite-head and output-tail bounds. Their sum
bounds the complete off-diagonal operator difference with fixed lp
majorants chosen before the omitted index and truncation cutoff.
-/

noncomputable section
open Set Complex Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- One lp majorant bounds every distinguished limit-operator column,
with the explicit finite-head and output-tail constants. -/
theorem SourceLemma12_4Data.originalLimitOperator_offDiagonal_column_head_tail
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (H : SourceLemma12_4Data hp hp1 W) (hW : IsOpen W)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c) (hV : IsOpen V)
    (φ : CoeffPair p) (hφW : φ ∈ W) (hφV : φ ∈ V)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (a : Coeff p) (ha : a ∈ sourcePsiOriginalRootPlacement D) :
    ∃ B : Coeff p, ∀ n : ℤ, n ≠ 0 → ∀ K : ℕ, 2*K ≤ n.natAbs →
      ‖Coeff.operatorOffDiagonal (sourcePsiOriginalLimitOperator hp hp1 a φ)
          (lp.single p n 1)‖ ≤
        (2/(n.natAbs:ℝ))*‖B‖ +
          ‖B-Coeff.truncate (Finset.Icc (-(K:ℤ)) (K:ℤ)) B‖ := by
  obtain ⟨U,_,hbase,_,C,_,hb⟩ :=
    H.originalLimitOperator_offDiagonal_locally_bounded hW hD hV φ hφW hφV a
  obtain ⟨B,_,hB⟩ := hb (a,φ) hbase hφ ha
  refine ⟨B,?_⟩
  intro n hn K hK
  apply Coeff.norm_le_reciprocal_column_head_tail n hn K hK _ B
  · exact Coeff.operatorOffDiagonal_diagonal _ n
  · intro m hmn
    rw [Coeff.operatorOffDiagonal_entry_other _ m n hmn]
    have hden : ‖((m-n:ℤ):ℂ)‖ = ((n-m).natAbs:ℝ) := by
      rw [Complex.norm_intCast,Int.cast_sub,abs_sub_comm,← Int.cast_sub,
        ← Int.cast_abs,← Int.natCast_natAbs]
      simp
    simpa only [hden] using hB m n hmn

/-- Holder's inequality controls the distinguished row by a fixed lp
coefficient and the actual conjugate-exponent lattice norm. -/
theorem SourceLemma12_4Data.originalLimitOperator_offDiagonal_row_bound
    {q : ℝ≥0∞} [Fact (1 ≤ q)] [p.HolderConjugate q]
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (H : SourceLemma12_4Data hp hp1 W) (hW : IsOpen W)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c) (hV : IsOpen V)
    (φ : CoeffPair p) (hφW : φ ∈ W) (hφV : φ ∈ V)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (a : Coeff p) (ha : a ∈ sourcePsiOriginalRootPlacement D) :
    ∃ B : Coeff p, ∀ n : ℤ, ∀ h : Coeff p,
      ‖(Coeff.operatorOffDiagonal (sourcePsiOriginalLimitOperator hp hp1 a φ) h) n‖ ≤
        (‖B n‖*‖Coeff.puncturedLattice q
          ((ENNReal.HolderConjugate.lt_top_iff_one_lt p q).mp hp.lt_top)‖)*‖h‖ := by
  obtain ⟨U,_,hbase,_,C,_,hb⟩ :=
    H.originalLimitOperator_offDiagonal_locally_bounded hW hD hV φ hφW hφV a
  obtain ⟨B,_,hB⟩ := hb (a,φ) hbase hφ ha
  refine ⟨B,?_⟩
  intro n h
  let T := Coeff.operatorOffDiagonal (sourcePsiOriginalLimitOperator hp hp1 a φ)
  have hoff (k : ℤ) (hkn : k ≠ n) :
      ‖(T (lp.single p k 1)) n‖ ≤ ‖B n‖/|((k-n:ℤ):ℝ)| := by
    dsimp only [T]
    rw [Coeff.operatorOffDiagonal_entry_other _ n k hkn.symm]
    have hden : ‖((n-k:ℤ):ℂ)‖ = |((k-n:ℤ):ℝ)| := by
      rw [Complex.norm_intCast]
      simp only [Int.cast_sub,abs_sub_comm]
    simpa only [hden] using hB n k hkn.symm
  obtain ⟨row,hr,hrep⟩ := Coeff.exists_operator_rowKernel_of_reciprocalEntries
    (q := q) hp n T B (Coeff.operatorOffDiagonal_diagonal _ n) hoff
  change ‖(T h) n‖ ≤ _
  rw [hrep h]
  exact (Coeff.norm_dualPairing_le h row).trans
    ((mul_le_mul_of_nonneg_left hr (norm_nonneg h)).trans_eq (by ring))


/-- The distinguished-column term on an arbitrary input has the same
head/tail bound times the input norm, with no extra constant. -/
theorem SourceLemma12_4Data.originalLimitOperator_offDiagonal_movingColumn_bound
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (H : SourceLemma12_4Data hp hp1 W) (hW : IsOpen W)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c) (hV : IsOpen V)
    (φ : CoeffPair p) (hφW : φ ∈ W) (hφV : φ ∈ V)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (a : Coeff p) (ha : a ∈ sourcePsiOriginalRootPlacement D) :
    ∃ B : Coeff p, ∀ n : ℤ, n ≠ 0 → ∀ K : ℕ, 2*K ≤ n.natAbs → ∀ h : Coeff p,
      ‖Coeff.operatorOffDiagonal (sourcePsiOriginalLimitOperator hp hp1 a φ)
          (lp.single p n (h n))‖ ≤
        ((2/(n.natAbs:ℝ))*‖B‖+
          ‖B-Coeff.truncate (Finset.Icc (-(K:ℤ)) (K:ℤ)) B‖)*‖h‖ := by
  obtain ⟨B,hB⟩ := H.originalLimitOperator_offDiagonal_column_head_tail hW hD hV φ hφW hφV hφ a ha
  refine ⟨B,?_⟩
  intro n hn K hK h
  have he : (lp.single p n (h n) : Coeff p) = h n • lp.single p n (1:ℂ) := by
    simpa only [smul_eq_mul,mul_one] using (lp.single_smul (E := fun _ : ℤ => ℂ) p n (h n) (1:ℂ))
  rw [he,map_smul,norm_smul,mul_comm]
  exact mul_le_mul (hB n hn K hK)
    (lp.norm_apply_le_norm (zero_lt_one.trans hp1).ne' h n) (norm_nonneg _) (by positivity)

end NLS.ZakharovShabat

noncomputable section
open Set Complex Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual off-diagonal error restricted to retained input and output
coordinates, the operator underlying term I in the source estimate. -/
def sourcePsiOriginalRetainedOffDiagonalDifference
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (a : Coeff p) (φ : CoeffPair p) :
    Coeff p →L[ℂ] Coeff p :=
  (Coeff.deleteCoordinate n).comp
    ((Coeff.operatorOffDiagonal (sourcePsiOriginalLimitOperator hp hp1 a φ)-
      Coeff.operatorOffDiagonal (sourcePsiOriginalFullRootJacobian hp hp1 n a φ)).comp
        (Coeff.deleteCoordinate n))

/-- On retained off-diagonal entries the restricted error is exactly
the difference of the actual original matrix entries. -/
theorem sourcePsiOriginalRetainedOffDiagonalDifference_entry
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m k : ℤ)
    (hmn : m ≠ n) (hkn : k ≠ n) (hkm : k ≠ m)
    (a : Coeff p) (φ : CoeffPair p) :
    (sourcePsiOriginalRetainedOffDiagonalDifference hp hp1 n a φ (lp.single p k 1)) m =
      (sourcePsiOriginalLimitOperator hp hp1 a φ (lp.single p k 1)) m-
        sourcePsiOriginalJacobianEntry hp hp1 n m k a φ := by
  have hdel : Coeff.deleteCoordinate n (lp.single p k 1) = lp.single p k 1 :=
    (Coeff.deleteCoordinate_eq_self_iff _ _).2 (by simp [lp.single_apply,Ne.symm hkn])
  simp only [sourcePsiOriginalRetainedOffDiagonalDifference,ContinuousLinearMap.comp_apply,
    hdel,Coeff.deleteCoordinate_apply_other n m hmn,sub_apply,lp.coeFn_sub,Pi.sub_apply,
    Coeff.operatorOffDiagonal_entry_other _ m k hkm.symm,
    sourcePsiOriginalFullRootJacobian_entry hp hp1 n m k hmn]

/-- The restricted error has zero diagonal, including the omitted index. -/
theorem sourcePsiOriginalRetainedOffDiagonalDifference_diagonal
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ) (a : Coeff p) (φ : CoeffPair p) :
    (sourcePsiOriginalRetainedOffDiagonalDifference hp hp1 n a φ (lp.single p m 1)) m = 0 := by
  by_cases hmn : m = n
  · subst m
    simp [sourcePsiOriginalRetainedOffDiagonalDifference]
  · have hdel : Coeff.deleteCoordinate n (lp.single p m 1) = lp.single p m 1 :=
      (Coeff.deleteCoordinate_eq_self_iff _ _).2 (by simp [lp.single_apply,Ne.symm hmn])
    simp only [sourcePsiOriginalRetainedOffDiagonalDifference,ContinuousLinearMap.comp_apply,
      hdel,Coeff.deleteCoordinate_apply_other n m hmn,sub_apply,lp.coeFn_sub,Pi.sub_apply,
      Coeff.operatorOffDiagonal_diagonal,sub_self]

/-- Term I has an explicit operator-norm head/tail bound with one actual
lp sequence before every omitted index and truncation cutoff. -/
theorem SourceLemma12_4Data.originalRetainedOffDiagonalDifference_head_tail
    {q : ℝ≥0∞} [Fact (1 ≤ q)] [p.HolderConjugate q]
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (H : SourceLemma12_4Data hp hp1 W)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c) (hV : IsOpen V)
    (φ : CoeffPair p) (hφW : φ ∈ W) (hφV : φ ∈ V)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (a : Coeff p) (ha : a ∈ sourcePsiOriginalRootPlacement D) :
    ∃ B : Coeff p, ∀ n : ℤ, n ≠ 0 → ∀ K : ℕ, 2*K ≤ n.natAbs →
      ‖sourcePsiOriginalRetainedOffDiagonalDifference hp hp1 n a φ‖ ≤
        ((2/(n.natAbs:ℝ))*‖B‖+‖B-Coeff.truncate (Finset.Icc (-(K:ℤ)) (K:ℤ)) B‖)*
          ‖Coeff.puncturedLattice q ((ENNReal.HolderConjugate.lt_top_iff_one_lt p q).mp hp.lt_top)‖ := by
  obtain ⟨B,hB⟩ := H.originalJacobian_offDiagonalDifference_majorant hD hV φ hφW hφV hφ a ha
  refine ⟨B,?_⟩
  intro n hn K hK
  apply Coeff.norm_operator_le_doubleReciprocal_head_tail hp n hn K hK _ B
  · intro k
    simp [sourcePsiOriginalRetainedOffDiagonalDifference]
  · exact fun m => sourcePsiOriginalRetainedOffDiagonalDifference_diagonal hp hp1 n m a φ
  · intro m k hmn hkm
    by_cases hkn : k = n
    · subst k
      have hdel : Coeff.deleteCoordinate n (lp.single p n (1:ℂ)) = 0 :=
        congrArg Subtype.val (Coeff.deleteCoordinateTo_single_same n (1:ℂ))
      simp only [sourcePsiOriginalRetainedOffDiagonalDifference,ContinuousLinearMap.comp_apply,
        hdel,map_zero,lp.coeFn_zero,Pi.zero_apply,norm_zero]
      positivity
    · rw [sourcePsiOriginalRetainedOffDiagonalDifference_entry hp hp1 n m k hmn hkn hkm,norm_sub_rev]
      have hden : ‖((n-m:ℤ):ℂ)‖ = ((n-m).natAbs:ℝ) := by
        rw [Complex.norm_intCast,← Int.cast_abs,← Int.natCast_natAbs]
        simp
      simpa only [hden,Complex.norm_intCast] using hB n m k hmn hkn hkm


/-- The three actual off-diagonal contributions give an explicit
operator-norm estimate with fixed lp majorants and vanishing output tails. -/
theorem SourceLemma12_4Data.originalFullRootJacobian_offDiagonal_head_tail
    {q : ℝ≥0∞} [Fact (1 ≤ q)] [p.HolderConjugate q]
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (H : SourceLemma12_4Data hp hp1 W) (hW : IsOpen W)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c) (hV : IsOpen V)
    (φ : CoeffPair p) (hφW : φ ∈ W) (hφV : φ ∈ V)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (a : Coeff p) (ha : a ∈ sourcePsiOriginalRootPlacement D) :
    ∃ Br Bi Bc : Coeff p, ∀ n : ℤ, n ≠ 0 → ∀ K : ℕ, 2*K ≤ n.natAbs →
      ‖Coeff.operatorOffDiagonal (sourcePsiOriginalLimitOperator hp hp1 a φ)-
        Coeff.operatorOffDiagonal (sourcePsiOriginalFullRootJacobian hp hp1 n a φ)‖ ≤
        (‖Br n‖+(2/(n.natAbs:ℝ))*‖Bi‖+
          ‖Bi-Coeff.truncate (Finset.Icc (-(K:ℤ)) (K:ℤ)) Bi‖)*
          ‖Coeff.puncturedLattice q ((ENNReal.HolderConjugate.lt_top_iff_one_lt p q).mp hp.lt_top)‖+
        (2/(n.natAbs:ℝ))*‖Bc‖+‖Bc-Coeff.truncate (Finset.Icc (-(K:ℤ)) (K:ℤ)) Bc‖ := by
  obtain ⟨Br,hBr⟩ := H.originalLimitOperator_offDiagonal_row_bound (q := q) hW hD hV φ hφW hφV hφ a ha
  obtain ⟨Bi,hBi⟩ := H.originalRetainedOffDiagonalDifference_head_tail (q := q) hD hV φ hφW hφV hφ a ha
  obtain ⟨Bc,hBc⟩ := H.originalLimitOperator_offDiagonal_movingColumn_bound hW hD hV φ hφW hφV hφ a ha
  refine ⟨Br,Bi,Bc,?_⟩
  intro n hn K hK
  let Q := Coeff.operatorOffDiagonal (sourcePsiOriginalLimitOperator hp hp1 a φ)
  let T := Q-Coeff.operatorOffDiagonal (sourcePsiOriginalFullRootJacobian hp hp1 n a φ)
  let Ti := sourcePsiOriginalRetainedOffDiagonalDifference hp hp1 n a φ
  let C := ‖Coeff.puncturedLattice q ((ENNReal.HolderConjugate.lt_top_iff_one_lt p q).mp hp.lt_top)‖
  let A := (2/(n.natAbs:ℝ))*‖Bi‖+‖Bi-Coeff.truncate (Finset.Icc (-(K:ℤ)) (K:ℤ)) Bi‖
  let B := (2/(n.natAbs:ℝ))*‖Bc‖+‖Bc-Coeff.truncate (Finset.Icc (-(K:ℤ)) (K:ℤ)) Bc‖
  have he : (‖Br n‖+(2/(n.natAbs:ℝ))*‖Bi‖+
      ‖Bi-Coeff.truncate (Finset.Icc (-(K:ℤ)) (K:ℤ)) Bi‖)*C+
      (2/(n.natAbs:ℝ))*‖Bc‖+‖Bc-Coeff.truncate (Finset.Icc (-(K:ℤ)) (K:ℤ)) Bc‖ =
        (‖Br n‖+A)*C+B := by dsimp only [A,B]; ring
  change ‖T‖ ≤ _
  rw [he]
  apply ContinuousLinearMap.opNorm_le_bound _ (by dsimp only [A,B,C]; positivity)
  intro h
  have hfull : T h = Coeff.deleteCoordinate n (T h)+lp.single p n ((T h) n) := by
    ext m
    by_cases hmn : m = n
    · subst m
      simp
    · simp [Coeff.deleteCoordinate_apply_other n m hmn,lp.single_apply,hmn]
  have hrow : (T h) n = (Q h) n := by
    simp only [T,sub_apply,lp.coeFn_sub,Pi.sub_apply,sourcePsiOriginal_offDiagonal_apply_same,sub_zero]
  have hret : Coeff.deleteCoordinate n (T h) =
      Ti h+Coeff.deleteCoordinate n (Q (lp.single p n (h n))) :=
    sourcePsiOriginal_offDiagonal_remainingRows_split hp hp1 n a φ h
  have hnorm : ‖T h‖ ≤ ‖Ti h‖+‖Coeff.deleteCoordinate n (Q (lp.single p n (h n)))‖+‖(Q h) n‖ := by
    have hb := norm_add_le (Coeff.deleteCoordinate n (T h)) (lp.single p n ((T h) n))
    rw [← hfull,lp.norm_single (zero_lt_one.trans hp1),hrow,hret] at hb
    exact hb.trans (add_le_add (norm_add_le _ _) (le_refl _))
  have hI : ‖Ti h‖ ≤ (A*C)*‖h‖ :=
    (Ti.le_opNorm h).trans (mul_le_mul_of_nonneg_right (hBi n hn K hK) (norm_nonneg h))
  have hdel (v : Coeff p) : ‖Coeff.deleteCoordinate n v‖ ≤ ‖v‖ := by
    apply lp.norm_mono (zero_lt_one.trans hp1).ne'
    intro m
    by_cases hmn : m = n
    · subst m
      simp
    · rw [Coeff.deleteCoordinate_apply_other n m hmn]
  have hII : ‖Coeff.deleteCoordinate n (Q (lp.single p n (h n)))‖ ≤ B*‖h‖ :=
    (hdel _).trans (hBc n hn K hK h)
  have hR : ‖(Q h) n‖ ≤ (‖Br n‖*C)*‖h‖ := hBr n h
  exact hnorm.trans ((add_le_add (add_le_add hI hII) hR).trans_eq (by ring))

end NLS.ZakharovShabat
