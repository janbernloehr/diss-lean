import NLS.ZakharovShabat.SourceSquaredGapNonSummability
import NLS.ZakharovShabat.SourceSquaredGapRowLowerBound
import NLS.ZakharovShabat.SourceRemark10_9LatticeTerm
import NLS.ZakharovShabat.SourceRemark10_9Taylor
import NLS.SequenceSpaces.TwoExponentMajorant

/-!
# An actual-source counterexample to the printed Remark 10.9 remainder

At p=8, subtracting the printed integer-lattice term can leave a disk
supremum outside ℓ², even for real potentials arbitrarily near zero.
The exact moving-denominator expansion remains valid. Every supremum
below is proved bounded above on the original disks before it is used.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The literal supremum with the signed sum printed in Remark 10.9. -/
def sourceRemark10_9PrintedSup (hp : p ≠ ⊤) (hp1 : 1 < p)
    (D : ℤ → Set ℂ) (ψ : CoeffPair p) (n : ℤ) : ℝ :=
  sSup ((fun z => ‖sourceMidpointQuotient hp hp1 ψ n z-1-
    sourceRemark10_9LatticeTerm hp hp1 ψ n‖) '' D n)

variable {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)} {D : ℤ → Set ℂ} {c : ℝ}

theorem SourceIsolatingNeighborhoods.printed_remainder_bddAbove
    (h : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (n : ℤ) :
    BddAbove ((fun z => ‖sourceMidpointQuotient hp hp1 ψ n z-1-
      sourceRemark10_9LatticeTerm hp hp1 ψ n‖) '' D n) := by
  obtain ⟨S,hS,_⟩ := exists_sourceSquaredGapPhysicalRows hp hp1 ψ
  obtain ⟨E,_,hE⟩ := h.midpoint_taylor_majorant_of_row ψ hψ S (fun k => (hS k).2) le_rfl
  refine ⟨‖E n‖+(c^2/4)*(∑' m,sourceSquaredGapReciprocalTerm hp hp1 ψ n m)/2+
    ‖sourceRemark10_9LatticeTerm hp hp1 ψ n‖,?_⟩
  rintro _ ⟨z,hz,rfl⟩
  dsimp only
  have hl := h.midpoint_radicand_summable ψ hψ n z hz
  have hlb : ‖sourceMidpointQuotientLinearTerm hp hp1 ψ n z‖ ≤
      (c^2/4)*(∑' m,sourceSquaredGapReciprocalTerm hp hp1 ψ n m)/2 := by
    rw [sourceMidpointQuotientLinearTerm,norm_div]
    norm_num only [Complex.norm_ofNat]
    exact div_le_div_of_nonneg_right ((norm_tsum_le_tsum_norm hl.1).trans hl.2) (by norm_num)
  have he : sourceMidpointQuotient hp hp1 ψ n z-1-sourceRemark10_9LatticeTerm hp hp1 ψ n =
      (sourceMidpointQuotient hp hp1 ψ n z-1-sourceMidpointQuotientLinearTerm hp hp1 ψ n z)+
        sourceMidpointQuotientLinearTerm hp hp1 ψ n z-sourceRemark10_9LatticeTerm hp hp1 ψ n := by ring
  rw [he]
  exact (norm_sub_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add (hE n z hz) hlb)) le_rfl)

theorem SourceIsolatingNeighborhoods.norm_le_printedSup
    (h : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (n : ℤ) (z : ℂ) (hz : z ∈ D n) :
    ‖sourceMidpointQuotient hp hp1 ψ n z-1-sourceRemark10_9LatticeTerm hp hp1 ψ n‖ ≤
      sourceRemark10_9PrintedSup hp hp1 D ψ n :=
  le_csSup (h.printed_remainder_bddAbove ψ hψ n) ⟨z,hz,rfl⟩

theorem SourceIsolatingNeighborhoods.printedSup_nonneg
    (h : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (n : ℤ) :
    0 ≤ sourceRemark10_9PrintedSup hp hp1 D ψ n := by
  obtain ⟨a,r,hr,he⟩ := h.discs n
  have ha : (a : ℂ) ∈ D n := by rw [he]; exact mem_ball_self hr
  exact (norm_nonneg _).trans (h.norm_le_printedSup ψ hψ n _ ha)

section Eight
local instance sourceRemarkEight : Fact (1 ≤ (8 : ℝ≥0∞)) := ⟨by norm_num⟩

/-- For actual real sources with nonsummable squared gaps, the printed
remainder cannot have an ℓ² majorant on any original isolating family. -/
theorem SourceIsolatingNeighborhoods.not_memℓp_printedSup_of_squaredGap
    {V : Set (CoeffPair 8)} {D : ℤ → Set ℂ} {c : ℝ}
    (h : SourceIsolatingNeighborhoods (p := 8) (by norm_num) (by norm_num) V D c)
    (ψ : CoeffPair 8) (hψ : ψ ∈ V)
    (hreal : IsRealType (CoeffPair.toMax 8 ψ))
    (hsmall : ‖sourcePeriodicMidpointDisplacement (p := 8) (by norm_num) (by norm_num) ψ‖ ≤ 1)
    (hgap : ¬ Memℓp (fun m : ℤ => (sourcePeriodicGapDisplacement (p := 8)
      (by norm_num) (by norm_num) ψ m)^2) 2) :
    ¬ Memℓp (fun n : ℤ => (sourceRemark10_9PrintedSup (p := 8)
      (by norm_num) (by norm_num) D ψ n : ℂ)) 2 := by
  let hp : (8 : ℝ≥0∞) ≠ ⊤ := by norm_num
  let hp1 : (1 : ℝ≥0∞) < 8 := by norm_num
  intro hsup
  let B : Coeff 2 := ⟨_,hsup⟩
  obtain ⟨S,hS,_⟩ := exists_sourceSquaredGapPhysicalRows hp hp1 ψ
  obtain ⟨E₀,_,hE₀⟩ := h.midpoint_taylor_majorant_of_row ψ hψ S (fun k => (hS k).2) le_rfl
  have h82 : (8 : ℝ≥0∞)/4 = 2 := by
    apply Eq.symm
    apply (ENNReal.eq_div_iff (by norm_num) (by norm_num)).mpr
    norm_num
  let E : Coeff 2 := ⟨fun n => E₀ n,by
    change Memℓp (fun n => E₀ n) 2
    simpa only [h82] using! lp.memℓp E₀⟩
  obtain ⟨N,hN⟩ := h.tail
  let row : ℤ → ℂ := fun n => ((∑' m,sourceSquaredGapReciprocalTerm hp hp1 ψ n m : ℝ):ℂ)
  have hpoint (n : ℤ) (hn : N+1 ≤ n.natAbs) :
      ‖row n‖ ≤ ‖((2 : ℂ) • B) n‖+‖((2 : ℂ) • E) n‖ := by
    have hz : (Real.pi : ℂ)*n ∈ D n := by
      rw [hN n (by omega)]
      exact mem_ball_self (by positivity : (0 : ℝ) < Real.pi/4)
    have hB : ‖sourceMidpointQuotient hp hp1 ψ n ((Real.pi : ℂ)*n)-1-
        sourceRemark10_9LatticeTerm hp hp1 ψ n‖ ≤ ‖B n‖ := by
      apply (h.norm_le_printedSup ψ hψ n _ hz).trans
      change sourceRemark10_9PrintedSup hp hp1 D ψ n ≤
        ‖(sourceRemark10_9PrintedSup hp hp1 D ψ n : ℂ)‖
      simpa only [Complex.norm_real,Real.norm_eq_abs] using le_abs_self _
    have hE := hE₀ n _ hz
    have hL := norm_sourceMidpointQuotientLinearTerm_freeCenter_le hp hp1 ψ hsmall n
    have hr : 0 ≤ ∑' m,sourceSquaredGapReciprocalTerm hp hp1 ψ n m := by
      apply tsum_nonneg
      intro m
      unfold sourceSquaredGapReciprocalTerm
      split_ifs <;> positivity
    have he : row n =
        (sourceMidpointQuotient hp hp1 ψ n ((Real.pi : ℂ)*n)-1-
          sourceMidpointQuotientLinearTerm hp hp1 ψ n ((Real.pi : ℂ)*n))-
        (sourceMidpointQuotient hp hp1 ψ n ((Real.pi : ℂ)*n)-1-
          sourceRemark10_9LatticeTerm hp hp1 ψ n)+
          sourceMidpointQuotientLinearTerm hp hp1 ψ n ((Real.pi : ℂ)*n) := by
      rw [sourceRemark10_9LatticeTerm_eq_physicalRow hp hp1 ψ hreal n]
      dsimp [row]
      ring
    have htri : ‖row n‖ ≤ ‖E n‖+‖B n‖+
        (∑' m,sourceSquaredGapReciprocalTerm hp hp1 ψ n m)/8 := by
      rw [he]
      exact (norm_add_le _ _).trans (add_le_add
        ((norm_sub_le _ _).trans (add_le_add hE hB)) hL)
    simp only [lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,norm_mul,Complex.norm_ofNat]
    simp only [row,Complex.norm_real,Real.norm_of_nonneg hr] at htri ⊢
    nlinarith [norm_nonneg (E n),norm_nonneg (B n)]
  obtain ⟨_,_,_,hrow⟩ := Coeff.exists_tailCoeff_of_twoSequenceMajorants
    (r := 2) (q := 2) (by norm_num) (by norm_num) (by norm_num) le_rfl
    row (N+1) ((2 : ℂ) • B) ((2 : ℂ) • E) hpoint
  exact hgap (memℓp_squared_sourceGap_of_physicalRows hp hp1 (by norm_num) ψ hrow)

/-- The printed estimate fails arbitrarily near zero, for actual real
potentials and a constructed original isolating-disk family. -/
theorem sourceRemark10_9_printed_counterexample
    (U : Set (CoeffPair 8)) (hU : IsOpen U) (hzero : (0 : CoeffPair 8) ∈ U) :
    ∃ ψ : CoeffPair 8, ψ ∈ U ∧ IsRealType (CoeffPair.toMax 8 ψ) ∧
      ∃ V : Set (CoeffPair 8), IsOpen V ∧ (0 : CoeffPair 8) ∈ V ∧ ψ ∈ V ∧
        ∃ D c, SourceIsolatingNeighborhoods (p := 8) (by norm_num) (by norm_num) V D c ∧
          ¬ Memℓp (fun n : ℤ => (sourceRemark10_9PrintedSup (p := 8)
            (by norm_num) (by norm_num) D ψ n : ℂ)) 2 := by
  let hp : (8 : ℝ≥0∞) ≠ ⊤ := by norm_num
  let hp1 : (1 : ℝ≥0∞) < 8 := by norm_num
  obtain ⟨N,ε,_,_,V,hV,_,hzeroV,c,hD⟩ :=
    exists_local_source_quantitative_isolating_discs hp hp1 0 (by simp)
  have hc := continuousAt_sourcePeriodicMidpointDisplacement_of_realType hp hp1 0 (by simp)
  obtain ⟨δ,hδ,hsmall⟩ := Metric.continuousAt_iff.mp hc 1 (by norm_num)
  obtain ⟨ψ,hψ,hreal,hgap⟩ := exists_near_zero_real_source_squaredGap_not_memℓp_two
    (U ∩ (V ∩ ball 0 δ)) (hU.inter (hV.inter isOpen_ball))
    ⟨hzero,hzeroV,mem_ball_self hδ⟩
  refine ⟨ψ,hψ.1,hreal,V,hV,hzeroV,hψ.2.1,_,c,hD,?_⟩
  apply hD.not_memℓp_printedSup_of_squaredGap ψ hψ.2.1 hreal _ hgap
  have hs := hsmall (mem_ball.mp hψ.2.2)
  rw [sourcePeriodicMidpointDisplacement_zero_source hp hp1,dist_zero_right] at hs
  exact hs.le

/-- At p=8 the printed sum of sequence classes is contained in ℓ²,
so it cannot absorb the remainder of the actual counterexample. -/
theorem sourceRemark10_9_printed_decomposition_counterexample
    (U : Set (CoeffPair 8)) (hU : IsOpen U) (hzero : (0 : CoeffPair 8) ∈ U) :
    ∃ ψ : CoeffPair 8, ψ ∈ U ∧ IsRealType (CoeffPair.toMax 8 ψ) ∧
      ∃ V : Set (CoeffPair 8), IsOpen V ∧ (0 : CoeffPair 8) ∈ V ∧ ψ ∈ V ∧
        ∃ D c, SourceIsolatingNeighborhoods (p := 8) (by norm_num) (by norm_num) V D c ∧
          ¬ ∃ A : Coeff ((8 : ℝ≥0∞)/4), ∃ B : CoeffOnePlus, ∀ n : ℤ,
            (sourceRemark10_9PrintedSup (p := 8) (by norm_num) (by norm_num) D ψ n : ℂ) =
              A n+B.1 n := by
  obtain ⟨ψ,hψ,hreal,V,hV,hzeroV,hψV,D,c,hD,hbad⟩ :=
    sourceRemark10_9_printed_counterexample U hU hzero
  refine ⟨ψ,hψ,hreal,V,hV,hzeroV,hψV,D,c,hD,?_⟩
  rintro ⟨A,B,he⟩
  apply hbad
  have h82 : (8 : ℝ≥0∞)/4 = 2 := by
    apply Eq.symm
    apply (ENNReal.eq_div_iff (by norm_num) (by norm_num)).mpr
    norm_num
  have hA : Memℓp (fun n => A n) 2 := by simpa only [h82] using! lp.memℓp A
  have hB : Memℓp B.1 2 := B.2 2 (by norm_num) (by norm_num)
  convert hA.add hB using 1
  funext n
  exact he n

end Eight
end NLS.ZakharovShabat
