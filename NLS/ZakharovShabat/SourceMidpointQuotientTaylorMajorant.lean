import NLS.ZakharovShabat.InverseSqrtProductTaylor
import NLS.ZakharovShabat.SourceMidpointQuotientTaylorGeometry
import NLS.SequenceSpaces.QuasiExponentEmbedding
import NLS.SequenceSpaces.QuasiHolderProduct

/-!
# Quarter-exponent majorants for the exact midpoint-quotient remainder

The square of the physical gap row gives an ℓ(p/4) majorant on every
original isolating disk. This includes all central indices and retains
the quasi-normed exponent when p is below four.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- An explicit uniform Taylor bound in terms of the separation and row norm. -/
def midpointQuotientTaylorConstant (c H : ℝ) : ℝ :=
  ((c^2)^2*Real.exp (c^2*((c^2/4)*H))+c^2+1/2)*(c^2/4)^2

theorem midpointQuotientTaylorConstant_nonneg (c H : ℝ) :
    0 ≤ midpointQuotientTaylorConstant c H := by
  unfold midpointQuotientTaylorConstant
  positivity

variable {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)} {D : ℤ → Set ℂ} {c : ℝ}

/-- The absolute radicand row controls the actual signed remainder on a full disk. -/
theorem SourceIsolatingNeighborhoods.midpoint_quotient_taylor_bound
    (h : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (n : ℤ) (z : ℂ) (hz : z ∈ D n)
    {H : ℝ} (hH : (∑' m, sourceSquaredGapReciprocalTerm hp hp1 ψ n m) ≤ H) :
    ‖sourceMidpointQuotient hp hp1 ψ n z-1-sourceMidpointQuotientLinearTerm hp hp1 ψ n z‖ ≤
      midpointQuotientTaylorConstant c H*(∑' m, sourceSquaredGapReciprocalTerm hp hp1 ψ n m)^2 := by
  obtain ⟨hs,hrow⟩ := h.midpoint_radicand_summable ψ hψ n z hz
  have hfactor := h.midpoint_inverse_sqrt_bound ψ hψ n
  have hQ := hrow.trans (mul_le_mul_of_nonneg_left hH (by positivity : 0 ≤ c^2/4))
  have ht := norm_tprod_inv_sqrt_taylor_le (sourceMidpointGapRadicand hp hp1 ψ n z)
    hs (fun m => (hfactor m z hz).1) (sq_nonneg c) (fun m => (hfactor m z hz).2) hQ
  rw [h.midpoint_quotient_product ψ hψ n z hz,sourceMidpointQuotientLinearTerm]
  apply ht.trans
  have hcoeff : 0 ≤ (c^2)^2*Real.exp (c^2*((c^2/4)*H))+c^2+1/2 := by positivity
  calc
    _ ≤ ((c^2)^2*Real.exp (c^2*((c^2/4)*H))+c^2+1/2)*
        ((c^2/4)*(∑' m, sourceSquaredGapReciprocalTerm hp hp1 ψ n m))^2 := by
      gcongr
    _ = _ := by unfold midpointQuotientTaylorConstant; ring

/-- Squaring one physical gap-row majorant retains the quarter exponent. -/
theorem SourceIsolatingNeighborhoods.midpoint_taylor_majorant_of_row
    (h : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψ : ψ ∈ V)
    (S : Coeff (ENNReal.ofReal (p.toReal/2)))
    (hS : ∀ n : ℤ, S n = ((∑' m, sourceSquaredGapReciprocalTerm hp hp1 ψ n m : ℝ):ℂ))
    {H : ℝ} (hH : ‖S‖ ≤ H) :
    ∃ E : Coeff (p/4), ‖E‖ ≤ midpointQuotientTaylorConstant c H*H^2 ∧
      ∀ n : ℤ, ∀ z ∈ D n,
        ‖sourceMidpointQuotient hp hp1 ψ n z-1-sourceMidpointQuotientLinearTerm hp hp1 ψ n z‖ ≤ ‖E n‖ := by
  let r := ENNReal.ofReal (p.toReal/2)
  have hpr : 0 < p.toReal := ENNReal.toReal_pos (zero_lt_one.trans hp1).ne' hp
  have hr : 0 < r.toReal := by dsimp [r]; rw [ENNReal.toReal_ofReal (by positivity)]; positivity
  have hr0 : r ≠ 0 := by intro he; simp [he] at hr
  have hrTop : r ≠ ⊤ := by dsimp [r]; simp
  have hhalf : 0 < (r/2).toReal := by rw [ENNReal.toReal_div]; norm_num; positivity
  have hquarter : 0 < (p/4).toReal := by rw [ENNReal.toReal_div]; norm_num; positivity
  have he : r/2 = p/4 := by
    dsimp [r]
    rw [Coeff.halfExponent_eq_div hp]
    simp only [div_eq_mul_inv,mul_assoc]
    congr 1
    rw [← ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
    norm_num
  let : r.HolderTriple r (r/2) := Coeff.holderTriple_half r
  let C := midpointQuotientTaylorConstant c H
  have hC : 0 ≤ C := midpointQuotientTaylorConstant_nonneg c H
  let T : Coeff (r/2) := (C:ℂ) • Coeff.quasiHolderProduct S S
  let E : Coeff (p/4) := ⟨fun n => T n,(lp.memℓp T).of_exponent_ge he.le⟩
  have hT (n : ℤ) : ‖E n‖ = C*‖S n‖^2 := by
    change ‖(C:ℂ)*(S n*S n)‖ = _
    rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg hC]
    ring
  have hS0 (n : ℤ) : 0 ≤ ∑' m, sourceSquaredGapReciprocalTerm hp hp1 ψ n m := by
    apply tsum_nonneg
    intro m
    unfold sourceSquaredGapReciprocalTerm
    split_ifs <;> positivity
  have hSn (n : ℤ) : ‖S n‖ = ∑' m, sourceSquaredGapReciprocalTerm hp hp1 ψ n m := by
    rw [hS,Complex.norm_real,Real.norm_of_nonneg (hS0 n)]
  refine ⟨E,?_,?_⟩
  · have hET : ‖E‖ ≤ ‖T‖ := Coeff.norm_quasiExponentInclusion_le
      (ENNReal.toReal_pos_iff.mp hhalf).1 (ENNReal.toReal_pos_iff.mp hquarter).1 (ENNReal.div_ne_top hp (by norm_num)) he.le T
    apply hET.trans
    rw [lp.norm_const_smul (ENNReal.toReal_pos_iff.mp hhalf).1.ne',Complex.norm_real,Real.norm_of_nonneg hC]
    have hprod := Coeff.norm_quasiHolderProduct_le (r := r/2) hr hr S S
    calc
      _ ≤ C*(‖S‖*‖S‖) := mul_le_mul_of_nonneg_left hprod hC
      _ ≤ C*H^2 := by
        apply mul_le_mul_of_nonneg_left _ hC
        nlinarith [lp.norm_nonneg' S]
  · intro n z hz
    rw [hT,hSn]
    exact h.midpoint_quotient_taylor_bound ψ hψ n z hz
      (by rw [← hSn]; exact (lp.norm_apply_le_norm hr0 S n).trans hH)

end NLS.ZakharovShabat
