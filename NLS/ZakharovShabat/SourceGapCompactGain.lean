import NLS.ZakharovShabat.SourceGapCompactEnvelope
import NLS.SequenceSpaces.SobolevFamilyBudget
import NLS.SequenceSpaces.SourceCotangent

/-!
# Uniform Sobolev gain for compact real-source families

A common weighted actual-gap majorant gives one full norm bound for the
stronger physical Fourier realizations of the entire compact family.
The positive gain retains the exact algebraic remainder threshold.
Continuity in the stronger norm is not assumed or inferred here.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A compact compatible real-source family gains a uniformly bounded
Sobolev weight from a common actual-gap majorant. Every original physical
Fourier coefficient, both components and the finite head are retained. -/
theorem exists_uniform_sobolev_gain_on_compact_source_family
    (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    {T : Type*} [TopologicalSpace T] [CompactSpace T] [Nonempty T]
    (φ : T → realTypeSourceSubmodule p) (ψ : T → WeightedCoeffPair w.toWeight p)
    (hφ : Continuous φ) (hψ : Continuous ψ)
    (hrel : ∀ t, w.forgetPairWeight (ψ t) = sourceWeightedPeriodOne (φ t).val)
    (s : ℝ) (hs : 0 < s) (hsp : s*p.toReal < min 1 (p.toReal-1))
    (Γ : Coeff p)
    (hΓs : Memℓp (fun n : ℤ => (Weight.sobolev s n:ℂ)*Γ n) p)
    (hΓ : ∀ t n, ‖(w (2*n):ℂ)*sourcePeriodicGapDisplacement hp hp1 (φ t).val n‖ ≤ ‖Γ n‖) :
    ∃ F : T → CoeffPair p,
      (∀ t n, (F t).fst n = (Weight.sobolev s n:ℂ)*((w n:ℂ)*(ψ t).fst.val n) ∧
        (F t).snd n = (Weight.sobolev s n:ℂ)*((w n:ℂ)*(ψ t).snd.val n)) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t, ‖F t‖ ≤ C := by
  have hpR : 1 < p.toReal := (ENNReal.toReal_lt_toReal (by simp) hp).mpr hp1
  have hp0 : 0 < p.toReal := zero_lt_one.trans hpR
  let G := fun N => ∑' n : ℤ, if N ≤ n.natAbs then ‖Γ n‖^p.toReal else 0
  have hG : ∀ N, 0 ≤ G N := fun N => tsum_nonneg (fun n => by split_ifs <;> positivity)
  have hGs (N : ℕ) : Summable (fun n : ℤ => if N ≤ n.natAbs then ‖Γ n‖^p.toReal else 0) :=
    (Γ.property.summable hp0).of_nonneg_of_le
      (fun n => by split_ifs <;> positivity) (fun n => by split_ifs <;> simp [Real.rpow_nonneg])
  have hgap : ∀ t N, sourceWeightedGapPowerTail hp hp1 w (φ t).val N ≤ G N := by
    intro t N
    have hpoint (n : ℤ) :
        (if N ≤ n.natAbs then ‖(w (2*n):ℂ)*sourcePeriodicGapDisplacement hp hp1 (φ t).val n‖^p.toReal else 0) ≤
          (if N ≤ n.natAbs then ‖Γ n‖^p.toReal else 0) := by
      split_ifs
      · exact Real.rpow_le_rpow (norm_nonneg _) (hΓ t n) hp0.le
      · exact le_rfl
    have hnonneg (n : ℤ) : 0 ≤
        (if N ≤ n.natAbs then ‖(w (2*n):ℂ)*sourcePeriodicGapDisplacement hp hp1 (φ t).val n‖^p.toReal else 0) := by
      split_ifs <;> positivity
    exact ((hGs N).of_nonneg_of_le hnonneg hpoint).tsum_le_tsum hpoint (hGs N)
  obtain ⟨V,M,hM,hV,hdom,_,htransfer⟩ :=
    exists_compact_source_summable_fourierTail_envelope hp hp1 w φ ψ hφ hψ hrel G hG hgap
  let r := (4:ℝ)^(s*p.toReal)
  have hr : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
  have hrα : r*(4:ℝ)^(-min 1 (p.toReal-1)) < 1 := by
    dsimp [r]
    rw [← Real.rpow_add (by norm_num)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hsp])
  have hfs : Summable (fun n : ℤ => (1+|(n:ℝ)|)^(s*p.toReal)*‖Γ n‖^p.toReal) := by
    apply (hΓs.summable hp0).congr
    intro n
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ((Weight.sobolev s).positive n),
      Real.mul_rpow ((Weight.sobolev s).positive n).le (norm_nonneg _),
      Weight.sobolev_apply,← Real.rpow_mul (by positivity)]
  have hgs : Summable (fun k => r^k*G (4*(4^k*M))) := by
    have h := summable_geometric_tails_of_summable_sobolev (fun n => ‖Γ n‖^p.toReal)
      (fun n => Real.rpow_nonneg (norm_nonneg _) _) (4*M) (by omega)
      (s*p.toReal) (mul_pos hs hp0) hfs
    simpa only [r,G,mul_assoc,mul_left_comm] using h
  have hVs := htransfer r hr hrα M le_rfl hgs
  obtain ⟨R₀,hR₀⟩ := isBounded_iff_forall_norm_le.mp (isCompact_univ.image hψ).isBounded
  let R := max R₀ 1
  have hR : 0 ≤ R := (by norm_num : (0:ℝ) ≤ 1).trans (le_max_right _ _)
  have hnorm (t : T) : ‖ψ t‖ ≤ R := (hR₀ _ ⟨t,mem_univ _,rfl⟩).trans (le_max_left _ _)
  let a := fun t => WeightedCoeff.weightEquiv w.toWeight p (ψ t).fst
  let b := fun t => WeightedCoeff.weightEquiv w.toWeight p (ψ t).snd
  have ha (t : T) : ‖a t‖ ≤ R := by
    rw [← WeightedCoeff.norm_eq]
    exact (WithLp.norm_fst_le (WeightedCoeff w.toWeight p) (ψ t)).trans (hnorm t)
  have hb (t : T) : ‖b t‖ ≤ R := by
    rw [← WeightedCoeff.norm_eq]
    exact (WithLp.norm_snd_le (WeightedCoeff w.toWeight p) (ψ t)).trans (hnorm t)
  have hat (t : T) (N : ℕ) : ‖Coeff.fourierTail N (a t)‖ ≤
      ‖weightedPairFourierTail w.toWeight N (ψ t)‖ := by
    rw [← WeightedCoeff.weightEquiv_fourierTail,← WeightedCoeff.norm_eq]
    exact WithLp.norm_fst_le (WeightedCoeff w.toWeight p) (weightedPairFourierTail w.toWeight N (ψ t))
  have hbt (t : T) (N : ℕ) : ‖Coeff.fourierTail N (b t)‖ ≤
      ‖weightedPairFourierTail w.toWeight N (ψ t)‖ := by
    rw [← WeightedCoeff.weightEquiv_fourierTail,← WeightedCoeff.norm_eq]
    exact WithLp.norm_snd_le (WeightedCoeff w.toWeight p) (weightedPairFourierTail w.toWeight N (ψ t))
  have hatV (t : T) (k : ℕ) : ‖Coeff.fourierTail (4^k*(2*M)) (a t)‖^p.toReal ≤ V (4^k*M) := by
    rw [show 4^k*(2*M) = 2*(4^k*M) by ring]
    exact (Real.rpow_le_rpow (norm_nonneg _) (hat t _) hp0.le).trans (hdom _ t)
  have hbtV (t : T) (k : ℕ) : ‖Coeff.fourierTail (4^k*(2*M)) (b t)‖^p.toReal ≤ V (4^k*M) := by
    rw [show 4^k*(2*M) = 2*(4^k*M) by ring]
    exact (Real.rpow_le_rpow (norm_nonneg _) (hbt t _) hp0.le).trans (hdom _ t)
  obtain ⟨F₁,hF₁,C₁,hC₁,hB₁⟩ := Coeff.exists_uniform_sobolev_family_of_geometric_tail_envelope
    hp a R hR ha (2*M) (by omega) s hs.le (fun k => V (4^k*M)) (fun k => hV _) hVs hatV
  obtain ⟨F₂,hF₂,C₂,hC₂,hB₂⟩ := Coeff.exists_uniform_sobolev_family_of_geometric_tail_envelope
    hp b R hR hb (2*M) (by omega) s hs.le (fun k => V (4^k*M)) (fun k => hV _) hVs hbtV
  let F := fun t => CoeffPair.inlCLM (F₁ t)+CoeffPair.inrCLM (F₂ t)
  refine ⟨F,?_,‖CoeffPair.inlCLM (p := p)‖*C₁+‖CoeffPair.inrCLM (p := p)‖*C₂,by positivity,?_⟩
  · intro t n
    constructor
    · change F₁ t n+0 = _
      rw [add_zero,hF₁]
      rfl
    · change 0+F₂ t n = _
      rw [zero_add,hF₂]
      rfl
  · intro t
    have h₁ := (CoeffPair.inlCLM (p := p)).le_opNorm (F₁ t)
    have h₂ := (CoeffPair.inrCLM (p := p)).le_opNorm (F₂ t)
    have hmul₁ := mul_le_mul_of_nonneg_left (hB₁ t) (norm_nonneg (CoeffPair.inlCLM (p := p)))
    have hmul₂ := mul_le_mul_of_nonneg_left (hB₂ t) (norm_nonneg (CoeffPair.inrCLM (p := p)))
    exact (norm_add_le _ _).trans (by linarith only [h₁,h₂,hmul₁,hmul₂])

end NLS.ZakharovShabat
