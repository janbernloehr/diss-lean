import NLS.ZakharovShabat.SourceStandardRootProductFactors
import NLS.SequenceSpaces.PuncturedLattice
import NLS.SequenceSpaces.HolderEmbedding

/-!
# Summable midpoint correction for the standard-root product

The free-parameter terms in Lemma 10.5 cancel between `k` and `-k`.
The remaining midpoint terms are the product of the source midpoint
displacement in `ℓᵖ` with the punctured reciprocal lattice in the
conjugate exponent. Hölder's inequality gives an actual `ℓ¹` sequence
and a tail estimate suitable for locally uniform product convergence.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The midpoint contribution `(τₖ-πk)/(πk)` for nonzero `k`, bundled
as an absolutely summable coefficient sequence. -/
def sourceStandardRootMidpointCorrection (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) : Coeff 1 := by
  letI : Fact (1 ≤ p.conjExponent) :=
    ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩
  let hq := (ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top
  exact (Real.pi : ℂ)⁻¹ •
    Coeff.holderProduct (q := 1) (sourcePeriodicMidpointDisplacement hp hp1 ψ)
      (Coeff.puncturedLattice p.conjExponent hq)

@[simp] theorem sourceStandardRootMidpointCorrection_apply
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (k : ℤ) :
    sourceStandardRootMidpointCorrection hp hp1 ψ k =
      if k = 0 then 0 else
        sourcePeriodicMidpointDisplacement hp hp1 ψ k / ((Real.pi : ℂ)*k) := by
  let : Fact (1 ≤ p.conjExponent) :=
    ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩
  simp only [sourceStandardRootMidpointCorrection, lp.coeFn_smul, Pi.smul_apply,
    smul_eq_mul, Coeff.holderProduct_apply, Coeff.puncturedLattice_apply]
  by_cases hk : k = 0
  · simp [hk]
  · simp only [if_neg hk]
    field_simp

/-- The midpoint correction is absolutely summable for every finite
source exponent. -/
theorem summable_norm_sourceStandardRootMidpointCorrection
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) :
    Summable (fun k : ℤ => ‖sourceStandardRootMidpointCorrection hp hp1 ψ k‖) := by
  simpa only [ENNReal.toReal_one, Real.rpow_one] using
    (lp.memℓp (sourceStandardRootMidpointCorrection hp hp1 ψ)).summable
      (by norm_num : 0 < (1 : ℝ≥0∞).toReal)

/-- The midpoint terms in the `k,-k` pairing form an absolutely
summable series on nonnegative indices. -/
theorem summable_norm_sourceStandardRootPairedMidpointCorrection
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) :
    Summable (fun k : ℕ =>
      ‖sourceStandardRootMidpointCorrection hp hp1 ψ (k : ℤ) +
        sourceStandardRootMidpointCorrection hp hp1 ψ (-(k : ℤ))‖) := by
  have hs := summable_norm_sourceStandardRootMidpointCorrection hp hp1 ψ
  have hpos : Summable (fun k : ℕ =>
      ‖sourceStandardRootMidpointCorrection hp hp1 ψ (k : ℤ)‖) :=
    hs.comp_injective Int.ofNat_injective
  have hneg : Summable (fun k : ℕ =>
      ‖sourceStandardRootMidpointCorrection hp hp1 ψ (-(k : ℤ))‖) :=
    hs.comp_injective (fun a b h => Int.ofNat_injective (neg_injective h))
  exact (hpos.add hneg).of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun k => norm_add_le _ _)

/-- The ℓ¹ tail is controlled by the source midpoint's ℓᵖ tail with
the same constant at every cutoff. -/
theorem norm_sourceStandardRootMidpointCorrection_tail_le
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (s : Finset ℤ) :
    ‖sourceStandardRootMidpointCorrection hp hp1 ψ -
      Coeff.truncate s (sourceStandardRootMidpointCorrection hp hp1 ψ)‖ ≤
      ‖(Real.pi : ℂ)⁻¹‖ *
        ‖sourcePeriodicMidpointDisplacement hp hp1 ψ -
          Coeff.truncate s (sourcePeriodicMidpointDisplacement hp hp1 ψ)‖ *
        ‖Coeff.puncturedLattice p.conjExponent
          ((ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top)‖ := by
  let : Fact (1 ≤ p.conjExponent) :=
    ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩
  let hq := (ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top
  have hcomm (a : Coeff p) :
      Coeff.truncate s (Coeff.holderProduct (q := 1) a
        (Coeff.puncturedLattice p.conjExponent hq)) =
      Coeff.holderProduct (q := 1) (Coeff.truncate s a)
        (Coeff.puncturedLattice p.conjExponent hq) := by
    ext k
    by_cases hk : k ∈ s <;>
      simp [Coeff.truncate_apply, Coeff.holderProduct_apply, hk]
  have heq : sourceStandardRootMidpointCorrection hp hp1 ψ -
      Coeff.truncate s (sourceStandardRootMidpointCorrection hp hp1 ψ) =
      (Real.pi : ℂ)⁻¹ •
        Coeff.holderProduct (q := 1)
          (sourcePeriodicMidpointDisplacement hp hp1 ψ -
            Coeff.truncate s (sourcePeriodicMidpointDisplacement hp hp1 ψ))
          (Coeff.puncturedLattice p.conjExponent hq) := by
    change (Real.pi : ℂ)⁻¹ •
      Coeff.holderProduct (q := 1) (sourcePeriodicMidpointDisplacement hp hp1 ψ)
        (Coeff.puncturedLattice p.conjExponent hq) -
      Coeff.truncate s ((Real.pi : ℂ)⁻¹ •
        Coeff.holderProduct (q := 1) (sourcePeriodicMidpointDisplacement hp hp1 ψ)
          (Coeff.puncturedLattice p.conjExponent hq)) = _
    rw [Coeff.truncate_smul, hcomm, ← smul_sub]
    simp only [map_sub]
    rfl
  rw [heq, norm_smul]
  calc
    _ ≤ ‖(Real.pi : ℂ)⁻¹‖ *
        (‖sourcePeriodicMidpointDisplacement hp hp1 ψ -
          Coeff.truncate s (sourcePeriodicMidpointDisplacement hp hp1 ψ)‖ *
          ‖Coeff.puncturedLattice p.conjExponent hq‖) :=
      mul_le_mul_of_nonneg_left
        (Coeff.norm_holderProduct_le
          (sourcePeriodicMidpointDisplacement hp hp1 ψ -
            Coeff.truncate s (sourcePeriodicMidpointDisplacement hp hp1 ψ))
          (Coeff.puncturedLattice p.conjExponent hq))
        (norm_nonneg _)
    _ = _ := by ring

/-- On a source neighborhood the midpoint contribution has uniformly
small ℓ¹ tails over symmetric frequency cutoffs. -/
theorem exists_uniform_small_sourceStandardRootMidpointCorrection
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∀ ψ ∈ V, ∀ M : ℕ, N ≤ M →
        ‖sourceStandardRootMidpointCorrection hp hp1 ψ -
          Coeff.truncate (Finset.Icc (-(M : ℤ)) M)
            (sourceStandardRootMidpointCorrection hp hp1 ψ)‖ ≤ ε := by
  let hq := (ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top
  let C : ℝ := ‖(Real.pi : ℂ)⁻¹‖ * ‖Coeff.puncturedLattice p.conjExponent hq‖
  have hC : 0 ≤ C :=
    mul_nonneg (norm_nonneg _) (lp.norm_nonneg' _)
  let δ : ℝ := ε / (C+1)
  have hCp : 0 < C+1 := by linarith
  have hδ : 0 < δ := div_pos hε hCp
  obtain ⟨N, _, V, hVopen, hφV, _, _, hdata⟩ :=
    exists_uniform_small_sourcePeriodicMidpointDisplacement hp hp1 φ hδ
  refine ⟨N, V, hVopen, hφV, ?_⟩
  intro ψ hψ M hM
  have ht := (hdata ψ hψ).2 M hM
  have hb := norm_sourceStandardRootMidpointCorrection_tail_le hp hp1 ψ
    (Finset.Icc (-(M : ℤ)) M)
  have heq : δ * (C+1) = ε := by
    dsimp [δ]
    field_simp
  calc
    _ ≤ ‖(Real.pi : ℂ)⁻¹‖ *
        ‖sourcePeriodicMidpointDisplacement hp hp1 ψ -
          Coeff.truncate (Finset.Icc (-(M : ℤ)) M)
            (sourcePeriodicMidpointDisplacement hp hp1 ψ)‖ *
        ‖Coeff.puncturedLattice p.conjExponent hq‖ := hb
    _ ≤ ‖(Real.pi : ℂ)⁻¹‖ * δ *
        ‖Coeff.puncturedLattice p.conjExponent hq‖ := by
          gcongr
          exact lp.norm_nonneg' _
    _ = C * δ := by dsimp [C]; ring
    _ ≤ ε := by nlinarith [hδ.le]

end NLS.ZakharovShabat
