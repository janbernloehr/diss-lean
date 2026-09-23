import NLS.ZakharovShabat.SourceStandardRootMidpointProduct
import NLS.SequenceSpaces.ReciprocalSeries

/-!
# Summable square-root remainder in the standard-root product

The principal-square-root correction to each normalized standard root
is `O(k⁻²)` once its midpoint is separated from a fixed spectral
parameter. The source midpoint and gap `ℓᵖ` norms give the required
global pointwise bounds, so the tail is absolutely summable.
-/

noncomputable section
open Complex Filter
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The square-root term in the exact factor decomposition. -/
def standardRootSqrtCorrection (t g d z : ℂ) : ℂ :=
  (t-z)/d * (Complex.sqrt (1-g/(4*(t-z)^2))-1)

/-- Rationalized control of the root correction away from the midpoint. -/
theorem norm_standardRootSqrtCorrection_le (t g d z : ℂ)
    (hd : d ≠ 0) (ht : t ≠ z) :
    ‖standardRootSqrtCorrection t g d z‖ ≤
      ‖g‖ / (4*‖d‖*‖t-z‖) := by
  have hdpos : 0 < ‖d‖ := norm_pos_iff.mpr hd
  have htpos : 0 < ‖t-z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr ht)
  unfold standardRootSqrtCorrection
  rw [norm_mul]
  calc
    _ ≤ ‖(t-z)/d‖ * ‖g/(4*(t-z)^2)‖ :=
      mul_le_mul_of_nonneg_left
        (norm_sqrt_one_sub_sub_one_le (g/(4*(t-z)^2))) (norm_nonneg _)
    _ = _ := by
      rw [norm_div, norm_div, norm_mul, norm_pow]
      norm_num only [Complex.norm_ofNat]
      field_simp

/-- If the midpoint is at least half a free denominator away, the
correction has the quadratic denominator required for summability. -/
theorem norm_standardRootSqrtCorrection_le_quadratic (t g d z : ℂ)
    (hd : d ≠ 0) (hsep : ‖d‖ ≤ 2*‖t-z‖) :
    ‖standardRootSqrtCorrection t g d z‖ ≤ ‖g‖ / (2*‖d‖^2) := by
  have hdpos : 0 < ‖d‖ := norm_pos_iff.mpr hd
  have htpos : 0 < ‖t-z‖ := by nlinarith
  have ht : t ≠ z := sub_ne_zero.mp (norm_pos_iff.mp htpos)
  have h := norm_standardRootSqrtCorrection_le t g d z hd ht
  have hden : 2*‖d‖^2 ≤ 4*‖d‖*‖t-z‖ := by nlinarith [mul_le_mul_of_nonneg_left hsep hdpos.le]
  calc
    _ ≤ ‖g‖ / (4*‖d‖*‖t-z‖) := h
    _ ≤ ‖g‖ / (2*‖d‖^2) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith [mul_le_mul_of_nonneg_left hden (norm_nonneg g)]

/-- A bounded midpoint offset and spectral parameter guarantee the
required separation at sufficiently distant free lattice points. -/
theorem free_midpoint_separation (t d z : ℂ)
    (hlarge : 2*(‖t-d‖+‖z‖) ≤ ‖d‖) :
    ‖d‖ ≤ 2*‖t-z‖ := by
  have h1 : ‖d‖ ≤ ‖d-t‖ + ‖t-z‖ + ‖z‖ := by
    have he : d = (d-t)+(t-z)+z := by ring
    calc
      ‖d‖ = ‖(d-t)+(t-z)+z‖ := congrArg norm he
      _ ≤ ‖(d-t)+(t-z)‖ + ‖z‖ := norm_add_le _ _
      _ ≤ ‖d-t‖ + ‖t-z‖ + ‖z‖ := by
        linarith [norm_add_le (d-t) (t-z)]
  rw [norm_sub_rev] at h1
  nlinarith

/-- The source square-root remainder, with the central factor omitted. -/
def sourceStandardRootSqrtCorrection (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (z : ℂ) (k : ℤ) : ℂ :=
  if k = 0 then 0 else
    standardRootSqrtCorrection
      (canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) k)
      ((canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) k)^2)
      ((Real.pi : ℂ)*k) z

/-- The source remainder is quadratically small once the free index
dominates the midpoint displacement and the spectral parameter. -/
theorem norm_sourceStandardRootSqrtCorrection_le (hp : p ≠ ⊤)
    (hp1 : 1 < p) (ψ : CoeffPair p) (z : ℂ) (k : ℤ)
    (hk : k ≠ 0)
    (hlarge : 2*(‖sourcePeriodicMidpointDisplacement hp hp1 ψ‖ + ‖z‖) ≤
      Real.pi*|(k : ℝ)|) :
    ‖sourceStandardRootSqrtCorrection hp hp1 ψ z k‖ ≤
      ‖sourcePeriodicGapDisplacement hp hp1 ψ‖^2 /
        (2*(Real.pi*|(k : ℝ)|)^2) := by
  let t := canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) k
  let γ := canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) k
  let d : ℂ := (Real.pi : ℂ)*k
  have hd : d ≠ 0 :=
    mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) (by exact_mod_cast hk)
  have hdn : ‖d‖ = Real.pi*|(k : ℝ)| := by
    simp [d, Complex.norm_intCast, abs_of_pos Real.pi_pos]
  have htbound : ‖t-d‖ ≤ ‖sourcePeriodicMidpointDisplacement hp hp1 ψ‖ := by
    simpa only [sourcePeriodicMidpointDisplacement_apply] using
      (lp.norm_apply_le_norm (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
        (sourcePeriodicMidpointDisplacement hp hp1 ψ) k)
  have hγbound : ‖γ‖ ≤ ‖sourcePeriodicGapDisplacement hp hp1 ψ‖ := by
    simpa only [sourcePeriodicGapDisplacement_apply] using
      (lp.norm_apply_le_norm (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
        (sourcePeriodicGapDisplacement hp hp1 ψ) k)
  have hsep : ‖d‖ ≤ 2*‖t-z‖ :=
    free_midpoint_separation t d z (by rw [hdn]; linarith)
  have h := norm_standardRootSqrtCorrection_le_quadratic t (γ^2) d z hd hsep
  have hdpos : 0 < ‖d‖ := norm_pos_iff.mpr hd
  simp only [sourceStandardRootSqrtCorrection, if_neg hk]
  change ‖standardRootSqrtCorrection t (γ^2) d z‖ ≤ _
  rw [hdn] at h
  calc
    _ ≤ ‖γ^2‖ / (2*(Real.pi*|(k : ℝ)|)^2) := h
    _ ≤ ‖sourcePeriodicGapDisplacement hp hp1 ψ‖^2 /
          (2*(Real.pi*|(k : ℝ)|)^2) := by
      rw [norm_pow]
      gcongr

/-- At each fixed source potential and spectral parameter the
square-root corrections are absolutely summable over all indices. -/
theorem summable_norm_sourceStandardRootSqrtCorrection (hp : p ≠ ⊤)
    (hp1 : 1 < p) (ψ : CoeffPair p) (z : ℂ) :
    Summable (fun k : ℤ => ‖sourceStandardRootSqrtCorrection hp hp1 ψ z k‖) := by
  let B : ℝ := ‖sourcePeriodicGapDisplacement hp hp1 ψ‖^2
  let A : ℝ := B / (2*Real.pi^2)
  have hbase : Summable (fun k : ℤ =>
      if k = 0 then (0 : ℝ) else |(k : ℝ)| ^ (-(2 : ℝ))) := by
    simpa only [zero_add] using
      (NLS.ReciprocalSeries.summable_int_shifted_rpow
        (α := 0) (q := 2) le_rfl (by norm_num))
  have hmajor : Summable (fun k : ℤ =>
      A * (if k = 0 then (0 : ℝ) else |(k : ℝ)| ^ (-(2 : ℝ)))) :=
    hbase.mul_left A
  obtain ⟨N, hN⟩ := exists_nat_gt
    (2*(‖sourcePeriodicMidpointDisplacement hp hp1 ψ‖+‖z‖)/Real.pi)
  have hevent : ∀ᶠ k : ℤ in cofinite, N < k.natAbs := by
    rw [Filter.eventually_cofinite]
    apply (Finset.Icc (-(N : ℤ)) N).finite_toSet.subset
    intro k hk
    simp only [Set.mem_ofPred_eq, not_lt] at hk
    simp only [Finset.mem_coe, Finset.mem_Icc]
    omega
  apply Summable.of_norm_bounded_eventually hmajor
  filter_upwards [hevent] with k hk
  have hk0 : k ≠ 0 := by omega
  have habs : |(k : ℝ)| = (k.natAbs : ℝ) := by
    simp only [Nat.cast_natAbs, Int.cast_abs]
  have hkr : (N : ℝ) < (k.natAbs : ℝ) := by exact_mod_cast hk
  have hlarge : 2*(‖sourcePeriodicMidpointDisplacement hp hp1 ψ‖+‖z‖) ≤
      Real.pi*|(k : ℝ)| := by
    rw [habs]
    have hlt := lt_trans hN hkr
    simpa only [mul_comm] using ((div_lt_iff₀ Real.pi_pos).mp hlt).le
  have hb := norm_sourceStandardRootSqrtCorrection_le hp hp1 ψ z k hk0 hlarge
  have hkpos : 0 < |(k : ℝ)| := abs_pos.mpr (by exact_mod_cast hk0)
  have heq : B / (2*(Real.pi*|(k : ℝ)|)^2) =
      A * |(k : ℝ)| ^ (-(2 : ℝ)) := by
    rw [Real.rpow_neg hkpos.le, Real.rpow_ofNat]
    dsimp [A]
    field_simp
  simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), if_neg hk0,
    B, ← heq] using hb

/-- Near any source potential and on any bounded spectral region, all
large-index square-root remainders share one summable quadratic bound. -/
theorem exists_uniform_sourceStandardRootSqrtCorrection_majorant
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (Rz : ℝ) :
    ∃ N : ℕ, ∃ V : Set (CoeffPair p), ∃ C : ℝ,
      IsOpen V ∧ φ ∈ V ∧ 0 ≤ C ∧
      (∀ ψ ∈ V, ∀ z : ℂ, ‖z‖ ≤ Rz → ∀ k : ℤ, N < k.natAbs →
        ‖sourceStandardRootSqrtCorrection hp hp1 ψ z k‖ ≤
          C * |(k : ℝ)| ^ (-(2 : ℝ))) ∧
      Summable (fun k : ℤ =>
        C * (if k = 0 then (0 : ℝ) else |(k : ℝ)| ^ (-(2 : ℝ)))) := by
  obtain ⟨_, _, V₁, hV₁open, hφV₁, R₁, hR₁, hdata₁⟩ :=
    exists_uniform_small_sourcePeriodicMidpointDisplacement hp hp1 φ
      (by norm_num : (0 : ℝ) < 1)
  obtain ⟨_, _, V₂, hV₂open, hφV₂, R₂, hR₂, hdata₂⟩ :=
    exists_uniform_small_sourcePeriodicGapDisplacement hp hp1 φ
      (by norm_num : (0 : ℝ) < 1)
  let C : ℝ := R₂^2 / (2*Real.pi^2)
  obtain ⟨N, hN⟩ := exists_nat_gt (2*(R₁+Rz)/Real.pi)
  refine ⟨N, V₁ ∩ V₂, C, hV₁open.inter hV₂open, ⟨hφV₁, hφV₂⟩,
    by dsimp [C]; positivity, ?_, ?_⟩
  · intro ψ hψ z hz k hk
    have hk0 : k ≠ 0 := by omega
    have habs : |(k : ℝ)| = (k.natAbs : ℝ) := by
      simp only [Nat.cast_natAbs, Int.cast_abs]
    have hkpos : 0 < |(k : ℝ)| := abs_pos.mpr (by exact_mod_cast hk0)
    have hkr : (N : ℝ) < (k.natAbs : ℝ) := by exact_mod_cast hk
    have hmid := (hdata₁ ψ hψ.1).1
    have hgap := (hdata₂ ψ hψ.2).1
    have hlarge : 2*(‖sourcePeriodicMidpointDisplacement hp hp1 ψ‖+‖z‖) ≤
        Real.pi*|(k : ℝ)| := by
      rw [habs]
      have hlt := lt_trans hN hkr
      have hbound := (div_lt_iff₀ Real.pi_pos).mp hlt
      nlinarith
    have hb := norm_sourceStandardRootSqrtCorrection_le hp hp1 ψ z k hk0 hlarge
    calc
      _ ≤ ‖sourcePeriodicGapDisplacement hp hp1 ψ‖^2 /
            (2*(Real.pi*|(k : ℝ)|)^2) := hb
      _ ≤ R₂^2 / (2*(Real.pi*|(k : ℝ)|)^2) := by gcongr
      _ = C * |(k : ℝ)| ^ (-(2 : ℝ)) := by
        rw [Real.rpow_neg hkpos.le, Real.rpow_ofNat]
        dsimp [C]
        field_simp
  · have hbase : Summable (fun k : ℤ =>
        if k = 0 then (0 : ℝ) else |(k : ℝ)| ^ (-(2 : ℝ))) := by
      simpa only [zero_add] using
        (NLS.ReciprocalSeries.summable_int_shifted_rpow
          (α := 0) (q := 2) le_rfl (by norm_num))
    exact hbase.mul_left C

end NLS.ZakharovShabat
