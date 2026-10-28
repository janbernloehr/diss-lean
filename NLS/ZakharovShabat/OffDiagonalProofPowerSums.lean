import NLS.ZakharovShabat.OffDiagonalProofRegions
import NLS.ZakharovShabat.DiagonalProofPowerSums

/-! # Literal regional power sums after (1.16)

Powered Young applies to the actual source regions, including their strict
half-cutoff. Exponent inclusion covers both source exponent regimes.
-/
noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)]

/-- Either exact source far moment has the printed two-kernel powered-Young budget. -/
theorem offDiagonalProofFarMoment_sum_le_kernel (hp : p ≠ ⊤) (hqt : q ≠ ⊤)
    (hr : 1 < r) (hrp : r ≤ p) (hrq : r ≤ q)
    (i : OffDiagonalProofRegion) (hi : i ≠ .near) (a : Coeff p) (N : ℕ) :
    Summable (fun n : ℤ => if N ≤ n.natAbs then (offDiagonalProofMoment q i a n)^(p.toReal/q.toReal) else 0) ∧
    (∑' n : ℤ, if N ≤ n.natAbs then (offDiagonalProofMoment q i a n)^(p.toReal/q.toReal) else 0) ≤
      (‖a‖*‖Coeff.fourierTail (N/2+1) (Coeff.puncturedLattice r hr)‖*‖Coeff.puncturedLattice r hr‖)^p.toReal := by
  obtain ⟨d,hd,hb⟩ := Coeff.exists_evenIteratedConvolutionRowNorm hp hrp a
    (Coeff.fourierTail (N/2+1) (Coeff.puncturedLattice r hr)) (Coeff.puncturedLattice r hr)
  have hrt : r ≠ ⊤ := ne_top_of_le_ne_top hp hrp
  have h := diagonalRow_power_sum_le hp (fun n => ‖offDiagonalProofRow (hr.trans_le hrq) i a n‖)
    N (fun _ => norm_nonneg _) d (fun n hn => ?_) _ hb
  · simpa only [offDiagonalProofMoment_power_eq (hr.trans_le hrq) hqt] using h
  · rw [hd,Complex.norm_real,norm_norm]
    exact (norm_offDiagonalProofRow_le_inner hr hrq i a n).trans
      (norm_offDiagonalProofFarRow_le hr hrt i hi a N n hn)

/-- The exact weak near region has the full potential-tail powered-Young budget. -/
theorem offDiagonalProofNearMoment_sum_le_kernel (hp : p ≠ ⊤) (hqt : q ≠ ⊤)
    (hr : 1 < r) (hrp : r ≤ p) (hrq : r ≤ q) (a : Coeff p) (N : ℕ) :
    Summable (fun n : ℤ => if N ≤ n.natAbs then (offDiagonalProofMoment q .near a n)^(p.toReal/q.toReal) else 0) ∧
    (∑' n : ℤ, if N ≤ n.natAbs then (offDiagonalProofMoment q .near a n)^(p.toReal/q.toReal) else 0) ≤
      (‖Coeff.fourierTail N a‖*‖Coeff.puncturedLattice r hr‖^2)^p.toReal := by
  obtain ⟨d,hd,hb⟩ := Coeff.exists_evenIteratedConvolutionRowNorm hp hrp (Coeff.fourierTail N a)
    (Coeff.puncturedLattice r hr) (Coeff.puncturedLattice r hr)
  have hb' : ‖d‖ ≤ ‖Coeff.fourierTail N a‖*‖Coeff.puncturedLattice r hr‖^2 := hb.trans_eq (by ring)
  have h := diagonalRow_power_sum_le hp (fun n => ‖offDiagonalProofRow (hr.trans_le hrq) .near a n‖)
    N (fun _ => norm_nonneg _) d (fun n hn => ?_) _ hb'
  · simpa only [offDiagonalProofMoment_power_eq (hr.trans_le hrq) hqt] using h
  · rw [hd,Complex.norm_real,norm_norm]
    exact (norm_offDiagonalProofRow_le_inner hr hrq .near a n).trans
      (norm_offDiagonalProofNearRow_le hr a N n hn)

/-- Every exact regional power sum converges when p is an admissible inner exponent. -/
theorem offDiagonalProofMoment_power_summable (hp : p ≠ ⊤) (hp1 : 1 < p)
    (hqt : q ≠ ⊤) (hpq : p ≤ q) (i : OffDiagonalProofRegion) (a : Coeff p) (N : ℕ) :
    Summable (fun n : ℤ => if N ≤ n.natAbs then (offDiagonalProofMoment q i a n)^(p.toReal/q.toReal) else 0) := by
  cases i with
  | farK => exact (offDiagonalProofFarMoment_sum_le_kernel hp hqt hp1 le_rfl hpq .farK (by decide) a N).1
  | farL => exact (offDiagonalProofFarMoment_sum_le_kernel hp hqt hp1 le_rfl hpq .farL (by decide) a N).1
  | near => exact (offDiagonalProofNearMoment_sum_le_kernel hp hqt hp1 le_rfl hpq a N).1

/-- The displayed low-exponent comparison is an inequality between convergent outer sums. -/
theorem offDiagonalProofMoment_sum_concave_le (hp : p ≠ ⊤) (hp1 : 1 < p)
    (hqt : q ≠ ⊤) (hpq : p ≤ q) (i : OffDiagonalProofRegion) (a : Coeff p) (N : ℕ) :
    Summable (fun n : ℤ => if N ≤ n.natAbs then offDiagonalProofMoment p i a n else 0) ∧
    (∑' n : ℤ, if N ≤ n.natAbs then (offDiagonalProofMoment q i a n)^(p.toReal/q.toReal) else 0) ≤
      ∑' n : ℤ, if N ≤ n.natAbs then offDiagonalProofMoment p i a n else 0 := by
  have hP := ENNReal.toReal_pos (zero_lt_one.trans hp1).ne' hp
  have hs : Summable (fun n : ℤ => if N ≤ n.natAbs then offDiagonalProofMoment p i a n else 0) := by
    simpa only [div_self hP.ne',Real.rpow_one] using
      offDiagonalProofMoment_power_summable hp hp1 hp le_rfl i a N
  refine ⟨hs,(offDiagonalProofMoment_power_summable hp hp1 hqt hpq i a N).tsum_le_tsum ?_ hs⟩
  intro n
  split_ifs
  · exact offDiagonalProofMoment_concave_le hp hp1 hqt hpq i a n
  · exact le_rfl

omit [Fact (1 ≤ r)] in
/-- The strict half-kernel has the same N-decay, including even and odd cutoffs. -/
theorem norm_offDiagonalProofHalfKernel_le (hr : 1 < r) {s : ℝ}
    (hc : s.HolderConjugate r.toReal) (N : ℕ) (hN : 0 < N) :
    ‖Coeff.fourierTail (N/2+1) (Coeff.puncturedLattice r hr)‖ ≤ 8*s*(N : ℝ)^(-(1/s)) := by
  exact (Coeff.norm_fourierTail_antitone (zero_lt_one.trans hr).ne'
    (Coeff.puncturedLattice r hr) (by omega : (N+1)/2 ≤ N/2+1)).trans
      (norm_diagonalHalfKernel_le hr hc N hN)

/-- One exponent-only constant for all literal regional power sums. -/
def offDiagonalProofRegionConstant (p : ℝ≥0∞) : ℝ :=
  (32*(max p.toReal p.conjExponent.toReal)^2)^p.toReal

omit [Fact (1 ≤ p)] in
theorem offDiagonalProofRegionConstant_pos (hp : p ≠ ⊤) (hp1 : 1 < p) :
    0 < offDiagonalProofRegionConstant p := by
  have hP := ENNReal.toReal_pos (zero_lt_one.trans hp1).ne' hp
  have hm : 0 < max p.toReal p.conjExponent.toReal := hP.trans_le (le_max_left _ _)
  unfold offDiagonalProofRegionConstant
  positivity

local instance : Fact (1 ≤ p.conjExponent) := ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩

/-- All actual regional sums converge; the far sums decay and the near sum retains the full potential tail. -/
theorem offDiagonalProofMoment_region_bounds (hp : p ≠ ⊤) (hp1 : 1 < p)
    (a : Coeff p) (N : ℕ) (hN : 0 < N) :
    (∀ i : OffDiagonalProofRegion, Summable (fun n : ℤ => if N ≤ n.natAbs then
      (offDiagonalProofMoment p.conjExponent i a n)^(p.toReal/p.conjExponent.toReal) else 0)) ∧
    (∀ i : OffDiagonalProofRegion, i ≠ .near →
      (∑' n : ℤ, if N ≤ n.natAbs then (offDiagonalProofMoment p.conjExponent i a n)^(p.toReal/p.conjExponent.toReal) else 0) ≤
        offDiagonalProofRegionConstant p*‖a‖^p.toReal/(N : ℝ)^(min 1 (p.toReal-1))) ∧
    (∑' n : ℤ, if N ≤ n.natAbs then (offDiagonalProofMoment p.conjExponent .near a n)^(p.toReal/p.conjExponent.toReal) else 0) ≤
      offDiagonalProofRegionConstant p*‖Coeff.fourierTail N a‖^p.toReal := by
  have hr := one_lt_diagonalInnerExponent hp hp1
  let : Fact (1 ≤ diagonalInnerExponent p) := ⟨hr.le⟩
  have hqt := ((ENNReal.HolderConjugate.lt_top_iff_one_lt p.conjExponent p).mpr hp1).ne
  obtain ⟨s,hc,hs,he⟩ := exists_diagonalInnerConjugate hp hp1
  have hs0 := hc.pos
  have hfar := fun i hi => offDiagonalProofFarMoment_sum_le_kernel hp hqt hr
    (min_le_left _ _) (min_le_right _ _) i hi a N
  have hnear := offDiagonalProofNearMoment_sum_le_kernel hp hqt hr
    (min_le_left _ _) (min_le_right _ _) a N
  have hC : (32*s^2)^p.toReal ≤ offDiagonalProofRegionConstant p := by
    apply Real.rpow_le_rpow (by positivity) _ ENNReal.toReal_nonneg
    gcongr
  refine ⟨?_,?_,?_⟩
  · intro i
    cases i with
    | farK => exact (hfar .farK (by decide)).1
    | farL => exact (hfar .farL (by decide)).1
    | near => exact hnear.1
  · intro i hi
    apply (hfar i hi).2.trans
    calc
      _ ≤ (‖a‖*(8*s*(N : ℝ)^(-(1/s)))*(4*s))^p.toReal := by
        apply Real.rpow_le_rpow (by positivity) _ ENNReal.toReal_nonneg
        gcongr
        · exact norm_offDiagonalProofHalfKernel_le hr hc N hN
        · exact Coeff.norm_puncturedLattice_le_four_conjugate hr hc
      _ = (32*s^2)^p.toReal*‖a‖^p.toReal/(N : ℝ)^(min 1 (p.toReal-1)) := by
        rw [show ‖a‖*(8*s*(N : ℝ)^(-(1/s)))*(4*s) = (32*s^2)*‖a‖*(N : ℝ)^(-(1/s)) by ring,
          Real.mul_rpow (by positivity) (by positivity),Real.mul_rpow (by positivity) (norm_nonneg _),
          ← Real.rpow_mul (Nat.cast_nonneg N)]
        have hexp : -(1/s)*p.toReal = -(min 1 (p.toReal-1)) := by rw [← he]; ring
        rw [hexp,Real.rpow_neg (Nat.cast_nonneg N),div_eq_mul_inv]
      _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hC (by positivity)) (by positivity)
  · apply hnear.2.trans
    calc
      _ ≤ (‖Coeff.fourierTail N a‖*(4*s)^2)^p.toReal := by
        apply Real.rpow_le_rpow (by positivity) _ ENNReal.toReal_nonneg
        gcongr
        exact Coeff.norm_puncturedLattice_le_four_conjugate hr hc
      _ ≤ (‖Coeff.fourierTail N a‖*(32*s^2))^p.toReal := by
        apply Real.rpow_le_rpow (by positivity) _ ENNReal.toReal_nonneg
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        nlinarith [sq_nonneg s]
      _ = (32*s^2)^p.toReal*‖Coeff.fourierTail N a‖^p.toReal := by
        rw [Real.mul_rpow (norm_nonneg _) (by positivity),mul_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_right hC (by positivity)

/-- Each literal far-region sum has N^(-1) decay at p>=2. -/
theorem offDiagonalProofFarMoment_sum_ge_two (hp : p ≠ ⊤) (hp1 : 1 < p) (hp2 : 2 ≤ p.toReal)
    (i : OffDiagonalProofRegion) (hi : i ≠ .near) (a : Coeff p) (N : ℕ) (hN : 0 < N) :
    (∑' n : ℤ, if N ≤ n.natAbs then (offDiagonalProofMoment p.conjExponent i a n)^(p.toReal/p.conjExponent.toReal) else 0) ≤
      offDiagonalProofRegionConstant p*‖a‖^p.toReal/N := by
  simpa only [min_eq_left (by linarith : 1 ≤ p.toReal-1),Real.rpow_one] using
    (offDiagonalProofMoment_region_bounds hp hp1 a N hN).2.1 i hi

/-- Each literal far-region sum has N^(-(p-1)) decay at 1<p<=2. -/
theorem offDiagonalProofFarMoment_sum_le_two (hp : p ≠ ⊤) (hp1 : 1 < p) (hp2 : p.toReal ≤ 2)
    (i : OffDiagonalProofRegion) (hi : i ≠ .near) (a : Coeff p) (N : ℕ) (hN : 0 < N) :
    (∑' n : ℤ, if N ≤ n.natAbs then (offDiagonalProofMoment p.conjExponent i a n)^(p.toReal/p.conjExponent.toReal) else 0) ≤
      offDiagonalProofRegionConstant p*‖a‖^p.toReal/(N : ℝ)^(p.toReal-1) := by
  simpa only [min_eq_right (by linarith : p.toReal-1 ≤ 1)] using
    (offDiagonalProofMoment_region_bounds hp hp1 a N hN).2.1 i hi

end NLS.ZakharovShabat
