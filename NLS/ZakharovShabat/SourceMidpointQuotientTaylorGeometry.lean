import NLS.ZakharovShabat.SourceQuotientAsymptoticGeometry
import NLS.ZakharovShabat.SourceSingleRootQuotientAbsolute

/-!
# Geometry for the midpoint-numerator product expansion

The original two-sided disk separation bounds the inverse square-root
factors even at central indices. The exact signed linear term retains
the moving midpoint denominator and its coefficient one eighth.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def sourceMidpointGapRadicand (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) (z : ℂ) (m : ℤ) : ℂ :=
  if m = n then 0 else sourceSingleRootGapRadicand hp hp1 ψ m z

def sourceMidpointQuotient (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) (z : ℂ) : ℂ :=
  sourceSingleRootQuotientJointProduct hp hp1 n
    (z,(sourcePeriodicMidpointDisplacement hp hp1 ψ,ψ))

def sourceMidpointQuotientLinearTerm (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) (z : ℂ) : ℂ :=
  (∑' m : ℤ, sourceMidpointGapRadicand hp hp1 ψ n z m)/2

/-- The coefficient and spectral dependence of the actual Taylor term. -/
theorem sourceMidpointQuotientLinearTerm_eq (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) (z : ℂ) :
    sourceMidpointQuotientLinearTerm hp hp1 ψ n z =
      ∑' m : ℤ, if m = n then 0 else
        (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)^2 /
          (8*(canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
            (periodOnePotential_mem ψ) m-z)^2) := by
  unfold sourceMidpointQuotientLinearTerm
  rw [← tsum_div_const]
  apply tsum_congr
  intro m
  by_cases hm : m = n
  · simp [sourceMidpointGapRadicand,hm]
  · simp only [sourceMidpointGapRadicand,if_neg hm,sourceSingleRootGapRadicand]
    rw [div_div]
    congr 1
    ring

variable {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)} {D : ℤ → Set ℂ} {c : ℝ}

/-- Disk separation controls all inverse roots, without a distant-index restriction. -/
theorem SourceIsolatingNeighborhoods.midpoint_inverse_sqrt_bound
    (h : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (n m : ℤ) (z : ℂ) (hz : z ∈ D n) :
    Complex.sqrt (1-sourceMidpointGapRadicand hp hp1 ψ n z m) ≠ 0 ∧
      ‖(Complex.sqrt (1-sourceMidpointGapRadicand hp hp1 ψ n z m))⁻¹‖ ≤ c^2 := by
  by_cases hm : m = n
  · have hc := h.one_le
    have hc2 : (1:ℝ) ≤ c^2 := by nlinarith
    simpa only [sourceMidpointGapRadicand,if_pos hm,sub_zero,Complex.sqrt_one,inv_one,norm_one] using And.intro (one_ne_zero : (1:ℂ) ≠ 0) hc2
  have hnm := Ne.symm hm
  let τ := canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m
  let w := sourceStandardRoot hp hp1 ψ m z
  let s := Complex.sqrt (1-sourceSingleRootGapRadicand hp hp1 ψ m z)
  let d := |((n-m:ℤ):ℝ)|
  have hc : 0 < c := zero_lt_one.trans_le h.one_le
  have hd : 0 < d := abs_pos.mpr (by exact_mod_cast sub_ne_zero.mpr hnm)
  have hwlow : c⁻¹*d ≤ ‖w‖ := (h.standardRoot_bounds ψ hψ n m hnm z hz).1
  have hwpos : 0 < ‖w‖ := (mul_pos (inv_pos.mpr hc) hd).trans_le hwlow
  have hw0 : w ≠ 0 := norm_pos_iff.mp hwpos
  have hw : w = (τ-z)*s := rfl
  have htz : τ-z ≠ 0 := by intro he; exact hw0 (by rw [hw,he,zero_mul])
  have hs : s ≠ 0 := by intro he; exact hw0 (by rw [hw,he,mul_zero])
  have he : s⁻¹ = (τ-z)/w := by rw [hw]; field_simp
  have htup : ‖τ-z‖ ≤ c*d := by
    have ht := (h.pointwise_distance n m hnm z hz _
      (h.gap ψ hψ m (sourcePeriodicMidpoint_mem_segment hp hp1 ψ m))).2
    rw [dist_comm,dist_eq_norm] at ht
    exact ht
  simp only [sourceMidpointGapRadicand,if_neg hm]
  refine ⟨hs,?_⟩
  change ‖s⁻¹‖ ≤ c^2
  rw [he,norm_div]
  apply (div_le_iff₀ hwpos).mpr
  calc
    _ ≤ c*d := htup
    _ = c^2*(c⁻¹*d) := by field_simp
    _ ≤ c^2*‖w‖ := mul_le_mul_of_nonneg_left hwlow (sq_nonneg _)

private theorem midpoint_squared_ratio_le
    (C d b g : ℝ) (hC : 1 ≤ C) (hd : 0 < d)
    (hsep : d ≤ C*b) :
    g^2/(4*b^2) ≤ (C^2/4)*(g^2*d^(-(2:ℝ))) := by
  have hCpos : 0 < C := by linarith
  have hbpos : 0 < b := by nlinarith
  have hd2 : d^2 ≤ C^2*b^2 := by
    calc
      d^2 ≤ (C*b)^2 := pow_le_pow_left₀ hd.le hsep 2
      _ = C^2*b^2 := by ring
  have hbase : (1:ℝ)/b^2 ≤ C^2/d^2 := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hbpos) (sq_pos_of_pos hd)).mpr
    nlinarith [hd2]
  calc
    g^2/(4*b^2) = (g^2/4)*(1/b^2) := by ring
    _ ≤ (g^2/4)*(C^2/d^2) :=
      mul_le_mul_of_nonneg_left hbase (by positivity)
    _ = (C^2/4)*(g^2*d^(-(2:ℝ))) := by
      rw [Real.rpow_neg hd.le]
      field_simp
      norm_num [Real.rpow_natCast]

/-- The radicand row is controlled on every original disk by the physical gap row. -/
theorem SourceIsolatingNeighborhoods.midpoint_radicand_bound
    (h : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (n : ℤ) (z : ℂ) (hz : z ∈ D n) (m : ℤ) :
    ‖sourceMidpointGapRadicand hp hp1 ψ n z m‖ ≤
      (c^2/4)*sourceSquaredGapReciprocalTerm hp hp1 ψ n m := by
  by_cases hm : m = n
  · simp [sourceMidpointGapRadicand,sourceSquaredGapReciprocalTerm,hm]
  have hd : 0 < |((n-m:ℤ):ℝ)| := abs_pos.mpr (by exact_mod_cast sub_ne_zero.mpr (Ne.symm hm))
  have he : sourceSquaredGapReciprocalTerm hp hp1 ψ n m =
      ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖^2*|((n-m:ℤ):ℝ)|^(-(2:ℝ)) := by
    simp only [sourceSquaredGapReciprocalTerm,if_neg hm]
    rw [show m-n = -(n-m) by ring,Int.cast_neg,abs_neg]
  simp only [sourceMidpointGapRadicand,if_neg hm,sourceSingleRootGapRadicand,
    norm_div,norm_pow,norm_mul,norm_ofNat,← sourcePeriodicGapDisplacement_apply,he]
  exact midpoint_squared_ratio_le c _ _ _ h.one_le hd (h.midpoint_separation ψ hψ n m (Ne.symm hm) z hz)

theorem SourceIsolatingNeighborhoods.midpoint_radicand_summable
    (h : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (n : ℤ) (z : ℂ) (hz : z ∈ D n) :
    Summable (fun m => ‖sourceMidpointGapRadicand hp hp1 ψ n z m‖) ∧
      (∑' m, ‖sourceMidpointGapRadicand hp hp1 ψ n z m‖) ≤
        (c^2/4)*(∑' m, sourceSquaredGapReciprocalTerm hp hp1 ψ n m) := by
  have ht := ((exists_sourceSquaredGapPhysicalRows hp hp1 ψ).choose_spec.1 n).1.mul_left (c^2/4)
  have hs := ht.of_nonneg_of_le (fun _ => norm_nonneg _) (h.midpoint_radicand_bound ψ hψ n z hz)
  exact ⟨hs,by simpa only [tsum_mul_left] using hs.tsum_le_tsum (h.midpoint_radicand_bound ψ hψ n z hz) ht⟩

/-- The actual midpoint-numerator quotient equals the unordered inverse-root product. -/
theorem SourceIsolatingNeighborhoods.midpoint_quotient_product
    (h : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (n : ℤ) (z : ℂ) (hz : z ∈ D n) :
    sourceMidpointQuotient hp hp1 ψ n z =
      ∏' m : ℤ, (Complex.sqrt (1-sourceMidpointGapRadicand hp hp1 ψ n z m))⁻¹ := by
  rw [sourceMidpointQuotient,← (hasProd_sourceSingleRootQuotientFactor hp hp1 ψ
    (sourcePeriodicMidpointDisplacement hp hp1 ψ) z n (h.disk_subset_omittedDomain ψ hψ n hz)).tprod_eq]
  apply tprod_congr
  intro m
  by_cases hm : m = n
  · simp [sourceSingleRootQuotientFactor,sourceMidpointGapRadicand,hm]
  have htz : canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m-z ≠ 0 := by
    intro he
    have hzmid := eq_of_sub_eq_zero he
    exact Set.disjoint_left.mp (h.disjoint n m (Ne.symm hm)) hz
      (hzmid ▸ h.gap ψ hψ m (sourcePeriodicMidpoint_mem_segment hp hp1 ψ m))
  simp only [sourceSingleRootQuotientFactor,sourceMidpointGapRadicand,if_neg hm,
    displacedRoots,sourcePeriodicMidpointDisplacement_apply]
  rw [show (Real.pi:ℂ)*m+(canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) m-(Real.pi:ℂ)*m) =
      canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m by ring]
  change _ / normalizedStandardRoot _ _ _ = _
  rw [singleRootQuotient_factor,div_self htz,one_mul]
  rfl

end NLS.ZakharovShabat
