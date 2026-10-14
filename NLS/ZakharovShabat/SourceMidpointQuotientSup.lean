import NLS.ZakharovShabat.SourceRemark10_9Taylor
import NLS.SequenceSpaces.TwoExponentMajorant

/-!
# The literal midpoint-numerator quotient supremum

The original disk supremum of `|Q_n-1|` is finite and nonnegative.
For p>2 it belongs to ℓ(p/2), on the same original disk families used
by the Taylor expansion. No index is dropped from the supremum sequence.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def sourceMidpointQuotientSup (hp : p ≠ ⊤) (hp1 : 1 < p)
    (D : ℤ → Set ℂ) (ψ : CoeffPair p) (n : ℤ) : ℝ :=
  sSup ((fun z => ‖sourceMidpointQuotient hp hp1 ψ n z-1‖) '' D n)

variable {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)} {D : ℤ → Set ℂ} {c : ℝ}

theorem SourceIsolatingNeighborhoods.norm_midpoint_linearTerm_le_row
    (h : SourceIsolatingNeighborhoods hp hp1 V D c) (ψ : CoeffPair p) (hψ : ψ ∈ V)
    (n : ℤ) (z : ℂ) (hz : z ∈ D n) :
    ‖sourceMidpointQuotientLinearTerm hp hp1 ψ n z‖ ≤
      (c^2/8)*(∑' m,sourceSquaredGapReciprocalTerm hp hp1 ψ n m) := by
  have hl := h.midpoint_radicand_summable ψ hψ n z hz
  rw [sourceMidpointQuotientLinearTerm,norm_div]
  norm_num only [Complex.norm_ofNat]
  have hb := div_le_div_of_nonneg_right ((norm_tsum_le_tsum_norm hl.1).trans hl.2)
    (by norm_num : (0 : ℝ) ≤ 2)
  apply hb.trans_eq
  ring

theorem SourceIsolatingNeighborhoods.midpoint_quotient_bddAbove
    (h : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (n : ℤ) :
    BddAbove ((fun z => ‖sourceMidpointQuotient hp hp1 ψ n z-1‖) '' D n) := by
  obtain ⟨S,hS,_⟩ := exists_sourceSquaredGapPhysicalRows hp hp1 ψ
  obtain ⟨E,_,hE⟩ := h.midpoint_taylor_majorant_of_row ψ hψ S (fun k => (hS k).2) le_rfl
  refine ⟨‖E n‖+(c^2/8)*(∑' m,sourceSquaredGapReciprocalTerm hp hp1 ψ n m),?_⟩
  rintro _ ⟨z,hz,rfl⟩
  dsimp only
  have he : sourceMidpointQuotient hp hp1 ψ n z-1 =
      (sourceMidpointQuotient hp hp1 ψ n z-1-sourceMidpointQuotientLinearTerm hp hp1 ψ n z)+
        sourceMidpointQuotientLinearTerm hp hp1 ψ n z := by ring
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add (hE n z hz) (h.norm_midpoint_linearTerm_le_row ψ hψ n z hz))

theorem SourceIsolatingNeighborhoods.norm_le_midpointQuotientSup
    (h : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (n : ℤ) (z : ℂ) (hz : z ∈ D n) :
    ‖sourceMidpointQuotient hp hp1 ψ n z-1‖ ≤ sourceMidpointQuotientSup hp hp1 D ψ n :=
  le_csSup (h.midpoint_quotient_bddAbove ψ hψ n) ⟨z,hz,rfl⟩

theorem SourceIsolatingNeighborhoods.midpointQuotientSup_nonneg
    (h : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (n : ℤ) :
    0 ≤ sourceMidpointQuotientSup hp hp1 D ψ n := by
  obtain ⟨a,r,hr,he⟩ := h.discs n
  have ha : (a : ℂ) ∈ D n := by rw [he]; exact mem_ball_self hr
  exact (norm_nonneg _).trans (h.norm_le_midpointQuotientSup ψ hψ n _ ha)

/-- The retained upper exponent on every original disk for p>2. -/
theorem SourceIsolatingNeighborhoods.memℓp_midpointQuotientSup_half
    (h : SourceIsolatingNeighborhoods hp hp1 V D c) (hp2 : 2 < p)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) :
    Memℓp (fun n : ℤ => (sourceMidpointQuotientSup hp hp1 D ψ n : ℂ)) (p/2) := by
  have hhalf : 1 < p/2 := by
    apply (ENNReal.lt_div_iff_mul_lt (Or.inl (by norm_num)) (Or.inl (by norm_num))).mpr
    simpa using hp2
  let : Fact (1 ≤ p/2) := ⟨hhalf.le⟩
  have hquarter : 0 < p/4 := ENNReal.div_pos (zero_lt_one.trans hp1).ne' (by norm_num)
  have hqh : p/4 ≤ p/2 := by gcongr; norm_num
  obtain ⟨S,hS,_⟩ := exists_sourceSquaredGapPhysicalRows hp hp1 ψ
  obtain ⟨E,_,hE⟩ := h.midpoint_taylor_majorant_of_row ψ hψ S (fun k => (hS k).2) le_rfl
  let Sh : Coeff (p/2) := ⟨fun n => S n,by
    change Memℓp (fun n => S n) (p/2)
    simpa only [Coeff.halfExponent_eq_div hp] using! lp.memℓp S⟩
  let A : Coeff (p/2) := ((c^2/8 : ℝ) : ℂ) • Sh
  have hA (n : ℤ) : ‖A n‖ = (c^2/8)*(∑' m,sourceSquaredGapReciprocalTerm hp hp1 ψ n m) := by
    have hn : 0 ≤ ∑' m,sourceSquaredGapReciprocalTerm hp hp1 ψ n m := by
      apply tsum_nonneg
      intro m
      unfold sourceSquaredGapReciprocalTerm
      split_ifs <;> positivity
    simp only [A,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,norm_mul,Sh,(hS n).2,
      Complex.norm_real,Real.norm_of_nonneg hn,Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ c^2/8)]
  obtain ⟨_,_,_,hfull⟩ := Coeff.exists_tailCoeff_of_twoSequenceMajorants
    hquarter hhalf (ENNReal.div_ne_top hp (by norm_num)) hqh
    (fun n => (sourceMidpointQuotientSup hp hp1 D ψ n : ℂ)) 0 A E (by
      intro n _
      rw [Complex.norm_real,Real.norm_of_nonneg (h.midpointQuotientSup_nonneg ψ hψ n)]
      obtain ⟨a,r,hr,he⟩ := h.discs n
      have hn : (D n).Nonempty := by rw [he]; exact nonempty_ball.mpr hr
      apply csSup_le (hn.image _)
      rintro _ ⟨z,hz,rfl⟩
      dsimp only
      have heq : sourceMidpointQuotient hp hp1 ψ n z-1 =
          sourceMidpointQuotientLinearTerm hp hp1 ψ n z+
          (sourceMidpointQuotient hp hp1 ψ n z-1-sourceMidpointQuotientLinearTerm hp hp1 ψ n z) := by ring
      rw [heq,hA]
      exact (norm_add_le _ _).trans (add_le_add (h.norm_midpoint_linearTerm_le_row ψ hψ n z hz) (hE n z hz)))
  exact hfull

end NLS.ZakharovShabat
