import NLS.FunctionalAnalysis.CompactTailEnvelope
import NLS.ZakharovShabat.SourceGapCompactRecurrence

/-!
# One forced scalar tail envelope for a compact real-source family

The family itself supplies a common weighted norm bound and uniformly
vanishing Fourier tails. A common actual gap-tail majorant then forces one
scalar quadratic recurrence, with constants chosen before the parameter.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A compact compatible source family with a common actual gap-tail
majorant has one vanishing scalar Fourier-tail envelope satisfying a
forced quadratic recurrence with uniform constants and cutoff. -/
theorem exists_compact_source_fourierTail_envelope
    (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    {T : Type*} [TopologicalSpace T] [CompactSpace T] [Nonempty T]
    (φ : T → realTypeSourceSubmodule p) (ψ : T → WeightedCoeffPair w.toWeight p)
    (hφ : Continuous φ) (hψ : Continuous ψ)
    (hrel : ∀ t, w.forgetPairWeight (ψ t) = sourceWeightedPeriodOne (φ t).val)
    (G : ℕ → ℝ)
    (hgap : ∀ t N, sourceWeightedGapPowerTail hp hp1 w (φ t).val N ≤ G N) :
    ∃ V : ℕ → ℝ, ∃ A B : ℝ, ∃ N₀ : ℕ, 0 ≤ A ∧ 0 ≤ B ∧ 2 ≤ N₀ ∧
      (∀ N, 0 ≤ V N) ∧
      (∀ N t, ‖weightedPairFourierTail w.toWeight (2*N) (ψ t)‖^p.toReal ≤ V N) ∧
      Tendsto V atTop (𝓝 0) ∧
      ∀ N : ℕ, N₀ ≤ N → V (4*N) ≤
        ((2:ℝ)^p.toReal*(2*(2:ℝ)^p.toReal))*G (4*N) +
          A/(4*N:ℝ)^(min 1 (p.toReal-1)) + B*(V N)^2 := by
  have hpR : 1 < p.toReal := (ENNReal.toReal_lt_toReal (by simp) hp).mpr hp1
  let f := fun N t => ‖weightedPairFourierTail w.toWeight (2*N) (ψ t)‖^p.toReal
  have hc : ∀ N, Continuous (f N) := fun N =>
    (((weightedPairFourierTail w.toWeight (2*N)).continuous.comp hψ).norm).rpow_const
      (fun _ => Or.inr ENNReal.toReal_nonneg)
  have hn : ∀ N t, 0 ≤ f N t := fun N t => Real.rpow_nonneg (norm_nonneg _) _
  have hm : ∀ t, Antitone (fun N => f N t) := by
    intro t M N hMN
    exact Real.rpow_le_rpow (norm_nonneg _)
      (norm_weightedPairFourierTail_antitone hp w.toWeight (ψ t) (Nat.mul_le_mul_left 2 hMN))
      ENNReal.toReal_nonneg
  have hcut : Tendsto (fun N : ℕ => 2*N) atTop atTop :=
    tendsto_atTop_mono (fun N => by dsimp; omega) tendsto_id
  have hl : ∀ t, Tendsto (fun N => f N t) atTop (𝓝 0) := by
    intro t
    have h : Tendsto (fun N => ‖weightedPairFourierTail w.toWeight (2*N) (ψ t)‖) atTop (𝓝 0) := by
      simpa only [norm_zero,Function.comp_def] using
        ((tendsto_weightedPairFourierTail hp w.toWeight (ψ t)).comp hcut).norm
    exact h.rpow_const_nhds_zero (by linarith only [hpR])
  obtain ⟨V,hV,hdom,hmax,hlim⟩ := exists_vanishing_max_envelope_on_compact f hc hn hm hl
  obtain ⟨R₀,hR₀⟩ := isBounded_iff_forall_norm_le.mp (isCompact_univ.image hψ).isBounded
  let R := max R₀ 1
  have hR : 0 ≤ R := (by norm_num : (0:ℝ) ≤ 1).trans (le_max_right _ _)
  have hnorm (t : T) : ‖ψ t‖ ≤ R := (hR₀ _ ⟨t,mem_univ _,rfl⟩).trans (le_max_left _ _)
  let C := (2:ℝ)^p.toReal
  let B := C*offDiagonalSummationConstant p*R^p.toReal
  let A := B*R^(2*p.toReal)
  have hB : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg (mul_nonneg (by dsimp [C]; positivity)
      (offDiagonalSummationConstant_nonneg p)) (Real.rpow_nonneg hR _)
  have hA : 0 ≤ A := mul_nonneg hB (Real.rpow_nonneg hR _)
  obtain ⟨N₀,hN₀,hrec⟩ := source_weighted_fourierTail_forced_recurrence_on_compact
    hp hp1 w φ ψ hφ hψ hrel
  refine ⟨V,A,B,N₀,hA,hB,hN₀,hV,hdom,hlim,fun N hN => ?_⟩
  obtain ⟨t,ht⟩ := hmax (4*N)
  rw [ht]
  have hpow := Real.rpow_le_rpow (norm_nonneg (ψ t)) (hnorm t) (ENNReal.toReal_nonneg (a := p))
  have hpow2 := Real.rpow_le_rpow (norm_nonneg (ψ t)) (hnorm t)
    (show 0 ≤ 2*p.toReal by positivity)
  have htail : ‖weightedPairFourierTail w.toWeight (2*N) (ψ t)‖^(2*p.toReal) ≤ (V N)^2 := by
    rw [mul_comm (2:ℝ),Real.rpow_mul (norm_nonneg _),Real.rpow_two]
    exact (sq_le_sq₀ (hn N t) (hV N)).mpr (hdom N t)
  have hsum : ‖ψ t‖^(2*p.toReal)/(4*N:ℝ)^(min 1 (p.toReal-1)) +
      ‖weightedPairFourierTail w.toWeight (2*N) (ψ t)‖^(2*p.toReal) ≤
        R^(2*p.toReal)/(4*N:ℝ)^(min 1 (p.toReal-1)) + (V N)^2 :=
    add_le_add (div_le_div_of_nonneg_right hpow2 (Real.rpow_nonneg (by positivity) _)) htail
  have herr : offDiagonalSummationConstant p*‖ψ t‖^p.toReal *
      (‖ψ t‖^(2*p.toReal)/(4*N:ℝ)^(min 1 (p.toReal-1)) +
        ‖weightedPairFourierTail w.toWeight (2*N) (ψ t)‖^(2*p.toReal)) ≤
      offDiagonalSummationConstant p*R^p.toReal *
        (R^(2*p.toReal)/(4*N:ℝ)^(min 1 (p.toReal-1))+(V N)^2) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hpow (offDiagonalSummationConstant_nonneg p))
      hsum (by positivity) (mul_nonneg (offDiagonalSummationConstant_nonneg p)
        (Real.rpow_nonneg hR _))
  have hb := (hrec t N hN).trans (mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left (hgap t (4*N)) (by positivity)) herr) (by positivity))
  change f (4*N) t ≤ _ at hb
  apply hb.trans_eq
  dsimp [A,B,C]
  ring

/-- One scalar envelope dominates every family member, and the same
geometric summability transfers from the common actual gap forcing for
every admissible geometric weight and every sufficiently large starting cutoff. -/
theorem exists_compact_source_summable_fourierTail_envelope
    (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    {T : Type*} [TopologicalSpace T] [CompactSpace T] [Nonempty T]
    (φ : T → realTypeSourceSubmodule p) (ψ : T → WeightedCoeffPair w.toWeight p)
    (hφ : Continuous φ) (hψ : Continuous ψ)
    (hrel : ∀ t, w.forgetPairWeight (ψ t) = sourceWeightedPeriodOne (φ t).val)
    (G : ℕ → ℝ) (hG : ∀ N, 0 ≤ G N)
    (hgap : ∀ t N, sourceWeightedGapPowerTail hp hp1 w (φ t).val N ≤ G N) :
    ∃ V : ℕ → ℝ, ∃ N₀ : ℕ, 2 ≤ N₀ ∧ (∀ N, 0 ≤ V N) ∧
      (∀ N t, ‖weightedPairFourierTail w.toWeight (2*N) (ψ t)‖^p.toReal ≤ V N) ∧
      Tendsto V atTop (𝓝 0) ∧
      ∀ r : ℝ, 0 < r → r*(4:ℝ)^(-min 1 (p.toReal-1)) < 1 →
        ∀ M : ℕ, N₀ ≤ M → Summable (fun k => r^k*G (4*(4^k*M))) →
          Summable (fun k => r^k*V (4^k*M)) := by
  obtain ⟨V,A,B,N₀,hA,_,hN₀,hV,hdom,hlim,hrec⟩ :=
    exists_compact_source_fourierTail_envelope hp hp1 w φ ψ hφ hψ hrel G hgap
  refine ⟨V,N₀,hN₀,hV,hdom,hlim,fun r hr hrα M hM hsum => ?_⟩
  let C := (2:ℝ)^p.toReal*(2*(2:ℝ)^p.toReal)
  have hα : 0 < min 1 (p.toReal-1) := by
    have hpR : 1 < p.toReal := (ENNReal.toReal_lt_toReal (by simp) hp).mpr hp1
    exact lt_min (by norm_num) (by linarith)
  apply summable_four_adic_of_forced_quadratic_tail V (fun N => C*G N)
    A B (min 1 (p.toReal-1)) r N₀ M hV
      (fun N => mul_nonneg (by dsimp [C]; positivity) (hG N)) hlim hA hα hr hrα
        (by omega) hM
  · exact (hsum.mul_left C).congr (fun k => by ring)
  · exact hrec

end NLS.ZakharovShabat
