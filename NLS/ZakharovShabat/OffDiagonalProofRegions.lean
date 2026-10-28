import NLS.ZakharovShabat.DoubleReciprocalSums
import NLS.SequenceSpaces.IteratedRowTails

/-! # The literal off-diagonal regions of Lemma 6.8

The strict far regions overlap. Their weak near complement includes equality.
Actual nested sequence rows identify the literal regional reciprocal moments.
-/
noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat

inductive OffDiagonalProofRegion
  | farK | farL | near
  deriving DecidableEq

/-- The integer cutoff for the strict source half-radius. -/
def offDiagonalProofCutoff (n : ℤ) : ℕ := n.natAbs/2+1

/-- The first normalized reciprocal coordinate is n-l. -/
def OffDiagonalProofRegion.left (i : OffDiagonalProofRegion) (n j : ℤ) : Prop :=
  match i with
  | .farK => True
  | .farL => offDiagonalProofCutoff n ≤ j.natAbs
  | .near => j.natAbs < offDiagonalProofCutoff n

/-- The second normalized reciprocal coordinate is n-k. -/
def OffDiagonalProofRegion.right (i : OffDiagonalProofRegion) (n k : ℤ) : Prop :=
  match i with
  | .farK => offDiagonalProofCutoff n ≤ k.natAbs
  | .farL => True
  | .near => k.natAbs < offDiagonalProofCutoff n

/-- The exact physical source region, with both resonant indices removed. -/
def OffDiagonalProofRegion.contains (i : OffDiagonalProofRegion) (n l k : ℤ) : Prop :=
  l ≠ n ∧ k ≠ n ∧ i.left n (n-l) ∧ i.right n (n-k)

instance (i : OffDiagonalProofRegion) (n j : ℤ) : Decidable (i.left n j) := by
  cases i <;> unfold OffDiagonalProofRegion.left <;> infer_instance
instance (i : OffDiagonalProofRegion) (n k : ℤ) : Decidable (i.right n k) := by
  cases i <;> unfold OffDiagonalProofRegion.right <;> infer_instance
instance (i : OffDiagonalProofRegion) (n l k : ℤ) : Decidable (i.contains n l k) :=
  inferInstanceAs (Decidable (l ≠ n ∧ k ≠ n ∧ i.left n (n-l) ∧ i.right n (n-k)))

theorem offDiagonalProofCutoff_iff (n j : ℤ) :
    offDiagonalProofCutoff n ≤ j.natAbs ↔ n.natAbs < 2*j.natAbs := by
  unfold offDiagonalProofCutoff; omega

theorem offDiagonalProofNear_iff (n j : ℤ) :
    j.natAbs < offDiagonalProofCutoff n ↔ 2*j.natAbs ≤ n.natAbs := by
  unfold offDiagonalProofCutoff; omega

/-- Every nonresonant pair belongs to at least one of the three source regions. -/
theorem offDiagonalProofRegions_cover (n l k : ℤ) (hl : l ≠ n) (hk : k ≠ n) :
    OffDiagonalProofRegion.farK.contains n l k ∨
    OffDiagonalProofRegion.farL.contains n l k ∨
    OffDiagonalProofRegion.near.contains n l k := by
  by_cases hK : offDiagonalProofCutoff n ≤ (n-k).natAbs
  · exact Or.inl ⟨hl,hk,trivial,hK⟩
  · by_cases hL : offDiagonalProofCutoff n ≤ (n-l).natAbs
    · exact Or.inr (Or.inl ⟨hl,hk,hL,trivial⟩)
    · exact Or.inr (Or.inr ⟨hl,hk,Nat.lt_of_not_ge hL,Nat.lt_of_not_ge hK⟩)

/-- The source near region is the complement of the union of the overlapping far regions. -/
theorem offDiagonalProofNear_complement (n l k : ℤ) (hl : l ≠ n) (hk : k ≠ n) :
    OffDiagonalProofRegion.near.contains n l k ↔
      ¬OffDiagonalProofRegion.farK.contains n l k ∧ ¬OffDiagonalProofRegion.farL.contains n l k := by
  constructor
  · rintro ⟨_,_,hL,hK⟩
    exact ⟨fun h => (Nat.not_le.mpr hK) h.2.2.2,fun h => (Nat.not_le.mpr hL) h.2.2.1⟩
  · rintro ⟨hK,hL⟩
    refine ⟨hl,hk,?_,?_⟩
    · exact Nat.lt_of_not_ge (fun h => hL ⟨hl,hk,h,trivial⟩)
    · exact Nat.lt_of_not_ge (fun h => hK ⟨hl,hk,trivial,h⟩)

/-- Near coordinates force both potential frequencies into their full-cutoff tails. -/
theorem offDiagonalProofNear_tail_indices (N : ℕ) (n j k : ℤ) (hn : N ≤ n.natAbs)
    (hj : j.natAbs < offDiagonalProofCutoff n) (hk : k.natAbs < offDiagonalProofCutoff n) :
    N ≤ (2*n-j).natAbs ∧ N ≤ (2*n-j-k).natAbs := by
  unfold offDiagonalProofCutoff at *
  omega

/-- The integer far cutoff is precisely the source strict real half-radius. -/
theorem offDiagonalProofCutoff_real_iff (n j : ℤ) :
    offDiagonalProofCutoff n ≤ j.natAbs ↔ |(n : ℝ)|/2 < |(j : ℝ)| := by
  rw [offDiagonalProofCutoff_iff]
  have hn : (n.natAbs : ℝ) = |(n : ℝ)| := by simp
  have hj : (j.natAbs : ℝ) = |(j : ℝ)| := by simp
  rw [← hn,← hj]
  constructor
  · intro h
    have hh : (n.natAbs : ℝ) < 2*(j.natAbs : ℝ) := by exact_mod_cast h
    linarith
  · intro h
    have hh : (n.natAbs : ℝ) < 2*(j.natAbs : ℝ) := by linarith
    exact_mod_cast hh

/-- The integer near window retains equality in the printed real half-radius. -/
theorem offDiagonalProofNear_real_iff (n j : ℤ) :
    j.natAbs < offDiagonalProofCutoff n ↔ |(j : ℝ)| ≤ |(n : ℝ)|/2 := by
  rw [← not_le,offDiagonalProofCutoff_real_iff,not_lt]

variable {p q r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)]

/-- Left kernel of an actual source region. -/
def offDiagonalProofLeftKernel (hq : 1 < q) (i : OffDiagonalProofRegion) (n : ℤ) : Coeff q :=
  match i with
  | .farK => Coeff.puncturedLattice q hq
  | .farL => Coeff.fourierTail (offDiagonalProofCutoff n) (Coeff.puncturedLattice q hq)
  | .near => Coeff.truncate (Coeff.lowFrequencies (offDiagonalProofCutoff n)) (Coeff.puncturedLattice q hq)

/-- Right kernel of an actual source region. -/
def offDiagonalProofRightKernel (hq : 1 < q) (i : OffDiagonalProofRegion) (n : ℤ) : Coeff q :=
  match i with
  | .farK => Coeff.fourierTail (offDiagonalProofCutoff n) (Coeff.puncturedLattice q hq)
  | .farL => Coeff.puncturedLattice q hq
  | .near => Coeff.truncate (Coeff.lowFrequencies (offDiagonalProofCutoff n)) (Coeff.puncturedLattice q hq)

omit [Fact (1 ≤ q)] in
theorem offDiagonalProofLeftKernel_apply (hq : 1 < q) (i : OffDiagonalProofRegion) (n j : ℤ) :
    offDiagonalProofLeftKernel hq i n j = if i.left n j then Coeff.puncturedLattice q hq j else 0 := by
  cases i <;> simp [offDiagonalProofLeftKernel,OffDiagonalProofRegion.left]

omit [Fact (1 ≤ q)] in
theorem offDiagonalProofRightKernel_apply (hq : 1 < q) (i : OffDiagonalProofRegion) (n k : ℤ) :
    offDiagonalProofRightKernel hq i n k = if i.right n k then Coeff.puncturedLattice q hq k else 0 := by
  cases i <;> simp [offDiagonalProofRightKernel,OffDiagonalProofRegion.right]

/-- A genuine nested sequence row for each literal source region. -/
def offDiagonalProofRow (hq : 1 < q) (i : OffDiagonalProofRegion) (a : Coeff p) (n : ℤ) : Coeff q :=
  Coeff.iteratedConvolutionRow a (offDiagonalProofLeftKernel hq i n) (offDiagonalProofRightKernel hq i n) (2*n)

/-- The literal summand in the source's regional conjugate moment. -/
def offDiagonalProofMomentTerm (q : ℝ≥0∞) (i : OffDiagonalProofRegion) (a : Coeff p) (n l k : ℤ) : ℝ :=
  if i.contains n l k then (‖a (l+k)‖ / |((n-l : ℤ) : ℝ)| / |((n-k : ℤ) : ℝ)|)^q.toReal else 0

/-- The literal regional moment, before taking its 1/q root. -/
def offDiagonalProofMoment (q : ℝ≥0∞) (i : OffDiagonalProofRegion) (a : Coeff p) (n : ℤ) : ℝ :=
  ∑' l : ℤ, ∑' k : ℤ, offDiagonalProofMomentTerm q i a n l k

omit [Fact (1 ≤ p)] [Fact (1 ≤ q)] in
/-- Exact term identity, including both removed zero denominators. -/
theorem offDiagonalProofMomentTerm_eq (hq : 1 < q) (hqt : q ≠ ⊤)
    (i : OffDiagonalProofRegion) (a : Coeff p) (n l k : ℤ) :
    offDiagonalProofMomentTerm q i a n l k =
      ‖a (2*n-(n-l)-(n-k)) * offDiagonalProofRightKernel hq i n (n-k) *
        offDiagonalProofLeftKernel hq i n (n-l)‖^q.toReal := by
  have hQ := ENNReal.toReal_pos (zero_lt_one.trans hq).ne' hqt
  rw [show 2*n-(n-l)-(n-k) = l+k by ring,
    offDiagonalProofLeftKernel_apply,offDiagonalProofRightKernel_apply]
  by_cases hl : l = n
  · subst l
    simp [offDiagonalProofMomentTerm,OffDiagonalProofRegion.contains,Real.zero_rpow hQ.ne']
  by_cases hk : k = n
  · subst k
    simp [offDiagonalProofMomentTerm,OffDiagonalProofRegion.contains,Real.zero_rpow hQ.ne']
  by_cases hL : i.left n (n-l) <;> by_cases hK : i.right n (n-k)
  all_goals simp only [offDiagonalProofMomentTerm,OffDiagonalProofRegion.contains,ne_eq,hl,hk,hL,hK,
    not_false_eq_true,if_true,if_false,and_false,and_true,mul_zero,zero_mul,norm_zero,
    Real.zero_rpow hQ.ne']
  simp only [norm_mul,norm_puncturedLattice_eq_inv_abs,div_eq_mul_inv]
  rw [mul_right_comm]

/-- The literal double moment is exactly the q-th power of the nested row norm. -/
theorem offDiagonalProofMoment_eq (hq : 1 < q) (hqt : q ≠ ⊤)
    (i : OffDiagonalProofRegion) (a : Coeff p) (n : ℤ) :
    offDiagonalProofMoment q i a n = ‖offDiagonalProofRow hq i a n‖^q.toReal := by
  rw [offDiagonalProofRow,Coeff.norm_iteratedConvolutionRow_rpow
    (ENNReal.toReal_pos (zero_lt_one.trans hq).ne' hqt)]
  conv_rhs => rw [← (Equiv.subLeft n).tsum_eq]
  apply tsum_congr
  intro l
  conv_rhs => rw [← (Equiv.subLeft n).tsum_eq]
  apply tsum_congr
  intro k
  exact offDiagonalProofMomentTerm_eq hq hqt i a n l k

/-- The regional moment converges jointly in its two physical indices. -/
theorem summable_offDiagonalProofMomentTerm (hq : 1 < q) (hqt : q ≠ ⊤)
    (i : OffDiagonalProofRegion) (a : Coeff p) (n : ℤ) :
    Summable (fun lk : ℤ × ℤ => offDiagonalProofMomentTerm q i a n lk.1 lk.2) := by
  have hs := ((Equiv.subLeft n).prodCongr (Equiv.subLeft n)).summable_iff.mpr
    (Coeff.summable_iteratedConvolutionRow_prod (ENNReal.toReal_pos (zero_lt_one.trans hq).ne' hqt)
      a (offDiagonalProofLeftKernel hq i n) (offDiagonalProofRightKernel hq i n) (2*n))
  exact hs.congr (fun lk => (offDiagonalProofMomentTerm_eq hq hqt i a n lk.1 lk.2).symm)

/-- Taking the p/q power gives the actual row norm to power p. -/
theorem offDiagonalProofMoment_power_eq (hq : 1 < q) (hqt : q ≠ ⊤)
    (i : OffDiagonalProofRegion) (a : Coeff p) (n : ℤ) :
    (offDiagonalProofMoment q i a n)^(p.toReal/q.toReal) = ‖offDiagonalProofRow hq i a n‖^p.toReal := by
  rw [offDiagonalProofMoment_eq hq hqt,← Real.rpow_mul (norm_nonneg _)]
  congr 1
  field_simp [(ENNReal.toReal_pos (zero_lt_one.trans hq).ne' hqt).ne']

/-- Pointwise contraction of both kernels contracts the actual nested row norm. -/
theorem norm_iteratedRow_mono_kernels (a : Coeff p) (b c b' c' : Coeff q) (m : ℤ)
    (hb : ∀ j, ‖b j‖ ≤ ‖b' j‖) (hc : ∀ k, ‖c k‖ ≤ ‖c' k‖) :
    ‖Coeff.iteratedConvolutionRow a b c m‖ ≤ ‖Coeff.iteratedConvolutionRow a b' c' m‖ := by
  have hq0 : q ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ q)).ne'
  apply lp.norm_mono hq0
  intro j
  simp only [Coeff.iteratedConvolutionRow_apply,norm_mul,Complex.norm_real,norm_norm]
  apply mul_le_mul _ (hb j) (norm_nonneg _) (norm_nonneg _)
  apply lp.norm_mono hq0
  intro k
  simp only [Coeff.convolutionRow_apply,norm_mul]
  exact mul_le_mul_of_nonneg_left (hc k) (norm_nonneg _)

/-- Increasing the inner exponent preserves both actual regional kernels. -/
theorem offDiagonalProofKernels_exponent (hr : 1 < r) (hrq : r ≤ q)
    (i : OffDiagonalProofRegion) (n : ℤ) :
    Coeff.exponentInclusion hrq (offDiagonalProofLeftKernel hr i n) =
      offDiagonalProofLeftKernel (hr.trans_le hrq) i n ∧
    Coeff.exponentInclusion hrq (offDiagonalProofRightKernel hr i n) =
      offDiagonalProofRightKernel (hr.trans_le hrq) i n := by
  constructor <;> ext j
  · simp only [Coeff.exponentInclusion_apply,offDiagonalProofLeftKernel_apply,Coeff.puncturedLattice_apply]
  · simp only [Coeff.exponentInclusion_apply,offDiagonalProofRightKernel_apply,Coeff.puncturedLattice_apply]

/-- Contractive exponent inclusion applies to each literal region. -/
theorem norm_offDiagonalProofRow_le_inner (hr : 1 < r) (hrq : r ≤ q)
    (i : OffDiagonalProofRegion) (a : Coeff p) (n : ℤ) :
    ‖offDiagonalProofRow (hr.trans_le hrq) i a n‖ ≤ ‖offDiagonalProofRow hr i a n‖ := by
  unfold offDiagonalProofRow
  rw [← (offDiagonalProofKernels_exponent hr hrq i n).1,
    ← (offDiagonalProofKernels_exponent hr hrq i n).2]
  exact Coeff.norm_iteratedConvolutionRow_exponent_le hrq _ _ _ _

/-- Either literal far region has the exact nested norm of one reciprocal kernel tail. -/
theorem norm_offDiagonalProofFarRow_eq (hq : 1 < q) (hqt : q ≠ ⊤)
    (i : OffDiagonalProofRegion) (hi : i ≠ .near) (a : Coeff p) (n : ℤ) :
    ‖offDiagonalProofRow hq i a n‖ = ‖doubleReciprocalFarRow hq a (offDiagonalProofCutoff n) n‖ := by
  cases i with
  | farK => exact doubleReciprocalFarRow_swap hq hqt a _ n
  | farL => rfl
  | near => exact (hi rfl).elim

/-- The strict source far cutoff retains its fixed kernel at floor(N/2)+1. -/
theorem norm_offDiagonalProofFarRow_le (hq : 1 < q) (hqt : q ≠ ⊤)
    (i : OffDiagonalProofRegion) (hi : i ≠ .near) (a : Coeff p) (N : ℕ) (n : ℤ) (hn : N ≤ n.natAbs) :
    ‖offDiagonalProofRow hq i a n‖ ≤ ‖doubleReciprocalFarRow hq a (N/2+1) n‖ := by
  rw [norm_offDiagonalProofFarRow_eq hq hqt i hi]
  apply norm_iteratedRow_mono_kernels a _ _ _ _ (2*n) _ (fun _ => le_rfl)
  intro j
  by_cases hj : offDiagonalProofCutoff n ≤ j.natAbs
  · have hN : N/2+1 ≤ j.natAbs := by unfold offDiagonalProofCutoff at hj; omega
    simp only [Coeff.fourierTail_apply,if_pos hj,if_pos hN,le_refl]
  · simp only [Coeff.fourierTail_apply,if_neg hj,norm_zero]
    exact norm_nonneg _

/-- On the exact weak near window, replacing the potential by its tail changes no row coefficient. -/
theorem offDiagonalProofNearRow_eq_tail (hq : 1 < q) (a : Coeff p) (N : ℕ)
    (n : ℤ) (hn : N ≤ n.natAbs) :
    offDiagonalProofRow hq .near a n = offDiagonalProofRow hq .near (Coeff.fourierTail N a) n := by
  ext j
  simp only [offDiagonalProofRow,Coeff.iteratedConvolutionRow_apply]
  by_cases hj : j.natAbs < offDiagonalProofCutoff n
  · have he : Coeff.convolutionRow a (offDiagonalProofRightKernel hq .near n) (2*n-j) =
        Coeff.convolutionRow (Coeff.fourierTail N a) (offDiagonalProofRightKernel hq .near n) (2*n-j) := by
      ext k
      by_cases hk : k.natAbs < offDiagonalProofCutoff n
      · have h := (offDiagonalProofNear_tail_indices N n j k hn hj hk).2
        simp only [Coeff.convolutionRow_apply,Coeff.fourierTail_apply,if_pos h]
      · simp [Coeff.convolutionRow_apply,offDiagonalProofRightKernel_apply,OffDiagonalProofRegion.right,hk]
    rw [he]
  · simp [offDiagonalProofLeftKernel_apply,OffDiagonalProofRegion.left,hj]

/-- The literal near row is bounded by the full double row of the retained potential tail. -/
theorem norm_offDiagonalProofNearRow_le (hq : 1 < q) (a : Coeff p) (N : ℕ)
    (n : ℤ) (hn : N ≤ n.natAbs) :
    ‖offDiagonalProofRow hq .near a n‖ ≤ ‖doubleReciprocalNearRow hq a N n‖ := by
  rw [offDiagonalProofNearRow_eq_tail hq a N n hn]
  exact (Coeff.norm_iteratedConvolutionRow_truncate_left_le
    (Coeff.fourierTail N a) (Coeff.puncturedLattice q hq)
    (Coeff.truncate (Coeff.lowFrequencies (offDiagonalProofCutoff n)) (Coeff.puncturedLattice q hq))
    (Coeff.lowFrequencies (offDiagonalProofCutoff n)) (2*n)).trans
    (Coeff.norm_iteratedConvolutionRow_truncate_right_le (Coeff.fourierTail N a)
      (Coeff.puncturedLattice q hq) (Coeff.puncturedLattice q hq)
      (Coeff.lowFrequencies (offDiagonalProofCutoff n)) (2*n))

/-- The source concavity step holds for all three actual regional moments. -/
theorem offDiagonalProofMoment_concave_le (hp : p ≠ ⊤) (hp1 : 1 < p) (hqt : q ≠ ⊤)
    (hpq : p ≤ q) (i : OffDiagonalProofRegion) (a : Coeff p) (n : ℤ) :
    (offDiagonalProofMoment q i a n)^(p.toReal/q.toReal) ≤ offDiagonalProofMoment p i a n := by
  rw [offDiagonalProofMoment_power_eq (hp1.trans_le hpq) hqt,offDiagonalProofMoment_eq hp1 hp]
  exact Real.rpow_le_rpow (norm_nonneg _) (norm_offDiagonalProofRow_le_inner hp1 hpq i a n) ENNReal.toReal_nonneg

end NLS.ZakharovShabat
