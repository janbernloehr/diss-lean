import NLS.ZakharovShabat.SourceSection23Original

/-!
# arXiv:1403.1369v2: main estimates

Article Theorems 1 and 2 (p. 3), Theorem 3 and Corollary 1 (p. 4).
The source family is constructed before all orders and weights. Integer
norms use the exact weight (1 + |2nπ|)^k and the component-sum Hilbert norm.
Weighted domains are expressed in their normalized Hilbert coordinates;
`normalizedWeightedSource` decodes by division by w(2n).

The nontrivial spectral and analytic proofs are reused from Section 23;
this module records article interfaces and normalization consequences.
-/

noncomputable section
open Set NLS.ZakharovShabat
namespace NLS.Articles.DNLSEstimates

/-- The article's ℓ¹_{2k} action norm, using the original indexed actions. -/
def actionMoment (φ : realTypeSourceSubmodule 2) (k : ℕ) : ℝ :=
  ∑' n : ℤ, sourceIndexedWeightedActionTerm φ k n

/-- The article uses a negative Fourier exponential in the first component.
Reflecting that component preserves the exact weighted energy, because the
spectral weight is even. This records the paper-to-library index convention. -/
theorem paper_weighted_source_norm_sq (w : SpectralWeight) (a : CoeffPair 2) :
    ‖a‖^2 = ∑' n : ℤ, (w (2*n))^2 *
      (‖(normalizedWeightedSource w a).fst (-n)‖^2 +
        ‖(normalizedWeightedSource w a).snd n‖^2) := by
  let b : CoeffPair 2 := WithLp.toLp 2 (Coeff.reflection a.fst, a.snd)
  have hb : ‖b‖^2 = ‖a‖^2 := by
    rw [WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2]
    change ‖Coeff.reflection a.fst‖^2 + ‖a.snd‖^2 = ‖a.fst‖^2 + ‖a.snd‖^2
    rw [Coeff.reflection.norm_map]
  have h := (normalizedWeightedSource_physical_norm w b).2
  rw [hb] at h
  calc
    ‖a‖^2 = _ := h
    _ = _ := by
      apply tsum_congr
      intro n
      simp [b, normalizedWeightedSource_fst, normalizedWeightedSource_snd]

variable {W₀ W V Wa B U : Set (CoeffPair 2)}
  {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
  {D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s}
  {A : SourceAbelianMomentAtlas (by simp) (by norm_num) Wa s}

/-- Every lower action moment used by Theorem 2 is an actually convergent sum. -/
theorem actionMoment_summable (m : ℕ) (hm : 1 ≤ m) (k : ℕ) (hk : k ≤ m)
    (a : realTypeHigherSobolevSourceLocus m) :
    Summable (sourceIndexedWeightedActionTerm
      ⟨higherSobolevSourceInclusion m a.val, a.property⟩ k) := by
  exact (sourceWeightedAction_summable_lower_on_Hm m hm k hk a).congr
    (fun n => (sourceIndexedWeightedActionTerm_eq _ k n).symm)

/-- The factor 1/2 in the article's action convention survives every Sobolev weight. -/
theorem actionMoment_eq_half_birkhoff_norm_sq
    (m : ℕ) (hm : 1 ≤ m) (k : ℕ) (hk : k ≤ m)
    (a : realTypeHigherSobolevSourceLocus m) :
    actionMoment ⟨higherSobolevSourceInclusion m a.val, a.property⟩ k =
      ‖D.complex.sobolevCoordinates m hm k hk a‖^2 / 2 := by
  have h := D.section23_sobolev_norm_sq m hm k hk a
  change _ = 2 * actionMoment _ k at h
  linarith

/-- At order zero the same action convention is half the physical pair mass. -/
theorem actionMoment_zero
    (m : ℕ) (a : realTypeHigherSobolevSourceLocus m) :
    actionMoment ⟨higherSobolevSourceInclusion m a.val, a.property⟩ 0 =
      ‖higherSobolevSourceInclusion m a.val‖^2 / 2 := by
  let φ : realTypeSourceSubmodule 2 :=
    ⟨higherSobolevSourceInclusion m a.val, a.property⟩
  change (∑' n : ℤ, sourceIndexedWeightedActionTerm φ 0 n) = ‖φ.val‖^2 / 2
  simp_rw [sourceIndexedWeightedActionTerm_eq]
  simp only [sourceWeightedActionTerm, Nat.mul_zero, pow_zero, one_mul,
    norm_sourceRealAction]
  exact sourceHilbert_sum_actions_eq_half_norm_sq φ

/-- Theorems 1 and 2, including the common-constant remark on p. 3.
The four fields `birkhoff_upper`, `birkhoff_lower`, `action_upper`, and
`action_lower` retain the powers 2m, 4m, and 4m-3 literally. Constants are
positive and chosen before all real H^m potentials. -/
theorem theorems_one_two (m : ℕ) (hm : 1 ≤ m) :
    ∃ c d : ℝ, SourceSection23SobolevBounds D m hm c d :=
  D.section23_sobolev_bounds m hm

/-- Theorem 3 on p. 4: a complex open neighborhood in the weighted Hilbert
coordinates, the weighted action bound there, and the actual real Birkhoff
image. A single positive constant is used in both bounds. -/
theorem theorem_three (Q : SourceSection23Data D A B U)
    (w : SpectralWeight) (hw : w.HasLinearFactor) :
    ∃ c : ℝ, 0 < c ∧ ∃ T : Set (CoeffPair 2),
      IsOpen T ∧ realTypeSourceLocus 2 ⊆ T ∧
      (∀ a ∈ T, normalizedWeightedSource w a ∈ U) ∧
      (∀ a ∈ T,
        Summable (fun n : ℤ => (w (2*n))^2 *
          ‖sourceIndexedAction (by simp) (by norm_num) n (normalizedWeightedSource w a)‖) ∧
        (∑' n : ℤ, (w (2*n))^2 *
          ‖sourceIndexedAction (by simp) (by norm_num) n (normalizedWeightedSource w a)‖) ≤
            c^2 * (w.realExtension (16*‖a‖^2))^2 * ‖a‖^2) ∧
      ∀ a : realTypeSourceSubmodule 2,
        ‖D.complex.m1Coordinates w hw a‖ ≤ c * w.realExtension (16*‖a.val‖^2) * ‖a.val‖ := by
  exact ⟨2048, by norm_num, Q.weighted w hw⟩

/-- Corollary 1 on p. 4, including the endpoint r=1. The open neighborhood
has the H^r norm topology, represented by normalized Hilbert coordinates.
The action estimate is valid on complex sources; the coordinate estimate
is asserted on the real subspace. -/
theorem corollary_one (Q : SourceSection23Data D A B U) (r : ℝ) (hr : 1 ≤ r) :
    ∃ c : ℝ, 0 < c ∧ ∃ T : Set (CoeffPair 2),
      IsOpen T ∧ realTypeSourceLocus 2 ⊆ T ∧
      (∀ a ∈ T, sourceRealSobolevInclusion r (zero_le_one.trans hr) a ∈ U) ∧
      (∀ a ∈ T,
        Summable (fun n : ℤ => (1+|((2*n:ℤ):ℝ)*Real.pi|)^(2*r) *
          ‖sourceIndexedAction (by simp) (by norm_num) n
            (sourceRealSobolevInclusion r (zero_le_one.trans hr) a)‖) ∧
        (∑' n : ℤ, (1+|((2*n:ℤ):ℝ)*Real.pi|)^(2*r) *
          ‖sourceIndexedAction (by simp) (by norm_num) n
            (sourceRealSobolevInclusion r (zero_le_one.trans hr) a)‖) ≤
          c^2 * (1+‖a‖)^(4*r) * ‖a‖^2) ∧
      ∀ a : realTypeSourceSubmodule 2,
        ‖D.complex.realSobolevCoordinates r hr a‖ ≤ c * (1+‖a.val‖)^(2*r) * ‖a.val‖ := by
  exact ⟨realSobolevEstimateConstant r, realSobolevEstimateConstant_pos r,
    Q.realSobolev r hr⟩

/-- One constructed original family underlies all four main article statements.
This closes the existence hypotheses of the interfaces above: the data are
not an essential unproved assumption supplied by the caller. -/
theorem exists_main_estimate_family :
    ∃ W₀ W V : Set (CoeffPair 2), ∃ s,
      ∃ D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s,
      ∃ Wa : Set (CoeffPair 2), ∃ A : SourceAbelianMomentAtlas (by simp) (by norm_num) Wa s,
      ∃ B U : Set (CoeffPair 2), SourceSection23Data D A B U :=
  sourceSection23_original_estimates

end NLS.Articles.DNLSEstimates
