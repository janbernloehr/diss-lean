import NLS.Articles.KdVKdV2Frequencies.SignedPhaseFlow
import NLS.Articles.KdVKdV2Frequencies.MassPhaseObstruction
import NLS.SequenceSpaces.NonnegativeEnergyDivergence
import NLS.SequenceSpaces.WeightedFiniteCoefficients
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Order.Filter.AtTopBot.Interval
import Mathlib.Tactic.FieldSimp

/-! # The exact KdV mass at the signed h^(1/2) endpoint

The normalization is H0 = sum_(n>=1) (2n*pi)|z_n|². Index zero is included
in the natural-index sum with coefficient zero. Finite mass is proved
equivalent to membership of the raw signed sequence in h^(1/2), rather than
being assumed as an independent hypothesis. This is the coordinate-space
mass-divergence dependency for arXiv:1605.06690v1, Theorem 1.12(v).
-/

noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal ComplexConjugate
namespace NLS.Articles.KdVKdV2Frequencies

def kdvMassTerm {w : Weight} (a : SignedCoordinates w 2) (n : ℕ) : ℝ :=
  (2 * (n : ℝ) * Real.pi) * ‖a.val.val (n : ℤ)‖ ^ 2

theorem kdvMassTerm_nonneg {w : Weight} (a : SignedCoordinates w 2) (n : ℕ) :
    0 ≤ kdvMassTerm a n := by
  unfold kdvMassTerm
  positivity

/-- Native h^(1/2) membership, preserving the original signed coefficients. -/
def HasHalfRegularity {w : Weight} (a : SignedCoordinates w 2) : Prop :=
  Memℓp (fun k => ((Weight.sobolev (1 / 2) k : ℝ) : ℂ) * a.val.val k) 2

private theorem half_term {w : Weight} (a : SignedCoordinates w 2) (k : ℤ) :
    ‖((Weight.sobolev (1 / 2) k : ℝ) : ℂ) * a.val.val k‖ ^ 2 =
      (1 + |(k : ℝ)|) * ‖a.val.val k‖ ^ 2 := by
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos ((Weight.sobolev (1 / 2)).positive k)]
  simp only [Weight.sobolev_apply, ← Real.sqrt_eq_rpow,
    Real.sq_sqrt (by positivity : 0 ≤ 1 + |(k : ℝ)|)]

/-- Finite KdV mass is exactly the required endpoint regularity, on the
zero-mode-free real signed locus, with all constants retained. -/
theorem hasHalfRegularity_iff_summable_kdvMassTerm {w : Weight}
    (a : SignedCoordinates w 2) :
    HasHalfRegularity a ↔ Summable (kdvMassTerm a) := by
  have hmem : HasHalfRegularity a ↔
      Summable (fun k : ℤ => (1 + |(k : ℝ)|) * ‖a.val.val k‖ ^ 2) := by
    unfold HasHalfRegularity
    rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, half_term]
  rw [hmem]
  constructor
  · intro h
    have hnat := h.comp_injective Int.ofNat_injective
    apply (hnat.mul_left (2 * Real.pi)).of_nonneg_of_le (kdvMassTerm_nonneg a)
    intro n
    change (2 * (n : ℝ) * Real.pi) * ‖a.val.val (n : ℤ)‖ ^ 2 ≤
      (2 * Real.pi) * ((1 + |(n : ℝ)|) * ‖a.val.val (n : ℤ)‖ ^ 2)
    rw [abs_of_nonneg (show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n)]
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ 2 * Real.pi by positivity)
      (sq_nonneg ‖a.val.val (n : ℤ)‖)]
  · intro h
    have hnat : Summable (fun n : ℕ => (1 + |((n : ℤ) : ℝ)|) * ‖a.val.val (n : ℤ)‖ ^ 2) := by
      apply (h.mul_left (1 / Real.pi)).of_nonneg_of_le (fun n => by positivity)
      intro n
      by_cases hn : n = 0
      · subst n
        simp [a.property.1, kdvMassTerm]
      · have hn' : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
        have he : (1 / Real.pi) * kdvMassTerm a n =
            2 * (n : ℝ) * ‖a.val.val (n : ℤ)‖ ^ 2 := by
          unfold kdvMassTerm
          field_simp
        rw [he]
        simp only [Int.cast_natCast, abs_of_nonneg (show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n)]
        nlinarith [sq_nonneg ‖a.val.val (n : ℤ)‖]
    apply summable_int_iff_summable_nat_and_neg.mpr
    refine ⟨hnat, ?_⟩
    simpa only [Int.cast_neg, abs_neg, a.property.2, Complex.norm_conj] using hnat

/-- Total mass is used only together with a finite-mass proof. The unrestricted
tsum is totalized by Lean and is not an extended-real definition at rough data. -/
def kdvFiniteMass {w : Weight} (a : SignedCoordinates w 2) : ℝ :=
  ∑' n : ℕ, kdvMassTerm a n

/-- Every coordinatewise endpoint-regular approximation to a rough signed
datum has diverging KdV mass, not merely one chosen truncation sequence. -/
theorem tendsto_kdvFiniteMass_atTop {w v : Weight} {ι : Type*} {l : Filter ι}
    (a : SignedCoordinates w 2) (ha : ¬ HasHalfRegularity a)
    (z : ι → SignedCoordinates v 2) (hz : ∀ i, HasHalfRegularity (z i))
    (hlim : ∀ n : ℤ, Tendsto (fun i => (z i).val.val n) l (𝓝 (a.val.val n))) :
    Tendsto (fun i => kdvFiniteMass (z i)) l atTop := by
  apply NLS.tendsto_atTop_of_nonsummable_coordinate_limit (kdvMassTerm a)
    (kdvMassTerm_nonneg a)
    (fun hs => ha ((hasHalfRegularity_iff_summable_kdvMassTerm a).mpr hs))
    (fun i => kdvMassTerm (z i)) (fun i => kdvFiniteMass (z i))
  · intro n
    exact ((hlim (n : ℤ)).norm.pow 2).const_mul _
  · intro i S
    exact ((hasHalfRegularity_iff_summable_kdvMassTerm (z i)).mp (hz i)).sum_le_tsum S
      (fun n _ => kdvMassTerm_nonneg (z i) n)

/-- Symmetric finite truncation preserves precisely the source's real locus. -/
def signedTruncate (w : Weight) (N : ℕ) (a : SignedCoordinates w 2) :
    SignedCoordinates w 2 :=
  ⟨WeightedCoeff.truncate w 2 (Finset.Icc (-(N : ℤ)) N) a.val, by
    constructor
    · simp [WeightedCoeff.truncate_apply, a.property.1]
    · intro k
      have hneg : -k ∈ Finset.Icc (-(N : ℤ)) N ↔ k ∈ Finset.Icc (-(N : ℤ)) N := by
        simp only [Finset.mem_Icc]
        omega
      by_cases hk : k ∈ Finset.Icc (-(N : ℤ)) N
      · simp [WeightedCoeff.truncate_apply, hk, hneg.mpr hk, a.property.2 k]
      · have hm : -k ∉ Finset.Icc (-(N : ℤ)) N := fun h => hk (hneg.mp h)
        simp [WeightedCoeff.truncate_apply, hk, hm]⟩

/-- These are actual norm-convergent approximants in the native signed space. -/
theorem tendsto_signedTruncate (w : Weight) (a : SignedCoordinates w 2) :
    Tendsto (fun N => signedTruncate w N a) atTop (𝓝 a) := by
  apply tendsto_subtype_rng.mpr
  simpa only [signedTruncate] using!
    (WeightedCoeff.tendsto_truncate w 2 (by norm_num) a.val).comp Finset.tendsto_Icc_neg

/-- Every finite truncation belongs to the endpoint space, even if the
original datum does not. No regularity or size assumption on w is needed. -/
theorem hasHalfRegularity_signedTruncate (w : Weight) (N : ℕ)
    (a : SignedCoordinates w 2) : HasHalfRegularity (signedTruncate w N a) := by
  have hf : Function.HasFiniteSupport (fun k : ℤ =>
      ((Weight.sobolev (1 / 2) k : ℝ) : ℂ) * (signedTruncate w N a).val.val k) := by
    apply (Finset.finite_toSet (Finset.Icc (-(N : ℤ)) N)).subset
    intro k hk
    change _ ≠ 0 at hk
    by_contra hnot
    apply hk
    change ((Weight.sobolev (1 / 2) k : ℝ) : ℂ) *
      (WeightedCoeff.truncate w 2 (Finset.Icc (-(N : ℤ)) N) a.val).val k = 0
    rw [WeightedCoeff.truncate_apply,
      if_neg (show k ∉ Finset.Icc (-(N : ℤ)) N from hnot), mul_zero]
  exact (memℓp_zero_iff.mpr hf).of_exponent_ge bot_le

theorem tendsto_signedTruncate_coefficient (w : Weight) (a : SignedCoordinates w 2) (k : ℤ) :
    Tendsto (fun N => (signedTruncate w N a).val.val k) atTop (𝓝 (a.val.val k)) := by
  have h := (continuous_subtype_val.tendsto a).comp (tendsto_signedTruncate w a)
  simpa only [Function.comp_def] using!
    ((WeightedCoeff.evalCLM w 2 k).continuous.tendsto a.val).comp h

/-- This explicitly constructs endpoint-regular approximants with mass
diverging at every datum outside h^(1/2), in the original weighted norm. -/
theorem tendsto_kdvFiniteMass_signedTruncate (w : Weight) (a : SignedCoordinates w 2)
    (ha : ¬ HasHalfRegularity a) :
    Tendsto (fun N => kdvFiniteMass (signedTruncate w N a)) atTop atTop :=
  tendsto_kdvFiniteMass_atTop a ha (fun N => signedTruncate w N a)
    (fun N => hasHalfRegularity_signedTruncate w N a)
    (tendsto_signedTruncate_coefficient w a)

/-- Every datum outside the endpoint has a nonzero positive coordinate,
so the phase obstruction always has an available mode. -/
theorem exists_positive_nonzero_of_not_hasHalfRegularity {w : Weight}
    (a : SignedCoordinates w 2) (ha : ¬ HasHalfRegularity a) :
    ∃ n : ℕ, 1 ≤ n ∧ a.val.val (n : ℤ) ≠ 0 := by
  by_contra h
  push Not at h
  have hz (n : ℕ) : a.val.val (n : ℤ) = 0 := by
    cases n with
    | zero => exact a.property.1
    | succ n => exact h (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
  apply ha
  apply (hasHalfRegularity_iff_summable_kdvMassTerm a).mpr
  have he : kdvMassTerm a = fun _ => 0 := by
    funext n
    simp only [kdvMassTerm, hz n, norm_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero]
  rw [he]
  exact summable_zero

/-- The endpoint condition, exact mass formula and finite approximants now
discharge the mass-divergence hypothesis of the earlier phase adapter.
Only the actual renormalized correction and its phase identity remain inputs.
This conclusion concerns uniform compact-time convergence, not fixed time. -/
theorem not_tendsto_kdv2_signedTruncate_phaseTrajectories (w : Weight)
    (a : SignedCoordinates w 2) (ha : ¬ HasHalfRegularity a)
    (n : ℕ) (hn : 1 ≤ n) (hamp : a.val.val (n : ℤ) ≠ 0)
    (T : ℝ) (hT : 0 < T) (correction : SignedCoordinates w 2 → ℝ)
    (hc : ContinuousAt correction a)
    (g : ℕ → C(Icc (0 : ℝ) T, ℂ))
    (he : ∀ N (τ : Icc (0 : ℝ) T), g N τ =
      Complex.exp (((-τ.val * kdv2FrequencyFromMass n
        (kdvFiniteMass (signedTruncate w N a)) (correction (signedTruncate w N a)) : ℝ) : ℂ) *
          Complex.I) * (signedTruncate w N a).val.val (n : ℤ))
    (G : C(Icc (0 : ℝ) T, ℂ)) : ¬ Tendsto g atTop (𝓝 G) :=
  not_tendsto_kdv2Mass_phaseTrajectories T hT n hn
    (fun N => kdvFiniteMass (signedTruncate w N a))
    (fun N => correction (signedTruncate w N a)) (correction a)
    (tendsto_kdvFiniteMass_signedTruncate w a ha)
    (hc.tendsto.comp (tendsto_signedTruncate w a))
    (fun N => (signedTruncate w N a).val.val (n : ℤ)) (a.val.val (n : ℤ)) hamp
    (tendsto_signedTruncate_coefficient w a (n : ℤ)) g he G

/-- No continuous extension of the positive-mode compact-time trajectory map
can agree with the KdV2 phase formula on these endpoint-regular approximants.
The actual spectral correction and physical phase identity are still required
before this can be applied to the equation's solution map. -/
theorem not_continuousAt_kdv2_modeTrajectory_extension (w : Weight)
    (a : SignedCoordinates w 2) (ha : ¬ HasHalfRegularity a)
    (n : ℕ) (hn : 1 ≤ n) (hamp : a.val.val (n : ℤ) ≠ 0)
    (T : ℝ) (hT : 0 < T) (correction : SignedCoordinates w 2 → ℝ)
    (hc : ContinuousAt correction a)
    (Q : SignedCoordinates w 2 → C(Icc (0 : ℝ) T, ℂ))
    (he : ∀ N (τ : Icc (0 : ℝ) T), Q (signedTruncate w N a) τ =
      Complex.exp (((-τ.val * kdv2FrequencyFromMass n
        (kdvFiniteMass (signedTruncate w N a)) (correction (signedTruncate w N a)) : ℝ) : ℂ) *
          Complex.I) * (signedTruncate w N a).val.val (n : ℤ)) :
    ¬ ContinuousAt Q a := by
  intro hQ
  exact not_tendsto_kdv2_signedTruncate_phaseTrajectories w a ha n hn hamp T hT correction hc
    (fun N => Q (signedTruncate w N a)) he (Q a)
    (hQ.tendsto.comp (tendsto_signedTruncate w a))

end NLS.Articles.KdVKdV2Frequencies
