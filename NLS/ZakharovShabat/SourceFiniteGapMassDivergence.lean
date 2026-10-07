import NLS.ZakharovShabat.SourceFiniteGapFrequencyExponent
import NLS.ZakharovShabat.SourceHilbertCoefficientCompactness
import NLS.ZakharovShabat.SourceFiniteGapDensity
import Mathlib.Topology.Sequences
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! # Physical mass diverges near non-Hilbert sources

A real source has a Hilbert representative exactly when its first Fourier
component is square summable. Any convergent finite-gap approximation to
a source outside this locus has mass tending to positive infinity. Finite
partial sums of coefficient energies already force this divergence.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The original Hilbert sources viewed in the larger source exponent. -/
def sourceHilbertLocus (h2p : 2 ≤ p) : Set (realTypeSourceSubmodule p) :=
  range (fun ψ : realTypeSourceSubmodule 2 =>
    (realTypeSourceExponentInclusion h2p ψ : realTypeSourceSubmodule p))

/-- Square summability characterizes the embedded original Hilbert source space. -/
theorem mem_sourceHilbertLocus_iff (h2p : 2 ≤ p) (φ : realTypeSourceSubmodule p) :
    φ ∈ sourceHilbertLocus h2p ↔ Summable (fun n : ℤ => ‖φ.val.fst n‖^2) := by
  constructor
  · rintro ⟨ψ,rfl⟩
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using!
      ψ.val.fst.property.summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  · intro h
    have hm : Memℓp (fun n => φ.val.fst n) 2 := by
      apply (memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).mpr
      simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using h
    let a : Coeff 2 := ⟨fun n => φ.val.fst n,hm⟩
    let ψ : realTypeSourceSubmodule 2 :=
      ⟨(CoeffPair.toMax 2).symm (a,star (Coeff.reflection a)),fun _ => rfl⟩
    refine ⟨ψ,?_⟩
    apply Subtype.ext
    apply (CoeffPair.toMax p).injective
    apply Prod.ext
    · ext n; rfl
    · ext n
      exact (φ.property n).symm

/-- The physical mass of a finite-gap source, computed by its coefficient-preserving model. -/
def sourceFiniteGapRealMass (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) : ℝ :=
  (sourceHilbertMass (sourceFiniteGapHilbertModel hp hp1 φ hf).val).re

/-- This is the original first physical Hamiltonian. -/
theorem sourceFiniteGapRealMass_eq_hamiltonian (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    sourceFiniteGapRealMass hp hp1 φ hf = (sourceFiniteGapNLSHamiltonian hp hp1 φ hf 1).re := by
  rw [← sourceFiniteGapHilbertModel_hamiltonian_one hp hp1 φ hf,
    sourceFiniteGapNLSHamiltonian_one_eq_mass]
  rfl

/-- On the real form the mass equals the first component's squared Hilbert norm. -/
theorem sourceFiniteGapRealMass_eq_norm (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    sourceFiniteGapRealMass hp hp1 φ hf = ‖(sourceFiniteGapHilbertModel hp hp1 φ hf).val.fst‖^2 := by
  let ψ := sourceFiniteGapHilbertModel hp hp1 φ hf
  change (sourceHilbertMass ψ.val).re = _
  have h := congrArg Complex.re (sourceHilbertMass_eq_half_norm_sq_of_realType ψ.val ψ.property)
  change (sourceHilbertMass ψ.val).re = ‖ψ‖^2/2 at h
  rw [h,realTypeSource_norm_sq_eq_two_mul_fst]
  ring

/-- Every finite partial sum of the original coefficient energy is bounded by physical mass. -/
theorem sum_fst_sq_le_sourceFiniteGapRealMass (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) (S : Finset ℤ) :
    ∑ n ∈ S, ‖φ.val.fst n‖^2 ≤ sourceFiniteGapRealMass hp hp1 φ hf := by
  rw [sourceFiniteGapRealMass_eq_norm]
  have h := lp.sum_rpow_le_norm_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    (sourceFiniteGapHilbertModel hp hp1 φ hf).val.fst S
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two,
    (sourceFiniteGapHilbertModel_coefficients hp hp1 φ hf _).1] using h

/-- Any convergent finite-gap approximation outside the Hilbert locus has diverging physical mass. -/
theorem tendsto_sourceFiniteGapRealMass_atTop (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : 2 ≤ p)
    {ι : Type*} {l : Filter ι} (φ : realTypeSourceSubmodule p)
    (hφ : φ ∉ sourceHilbertLocus h2p) (ψ : ι → realTypeSourceSubmodule p)
    (hf : ∀ j, ψ j ∈ sourceFiniteGapLocus hp hp1) (hψ : Tendsto ψ l (𝓝 φ)) :
    Tendsto (fun j => sourceFiniteGapRealMass hp hp1 (ψ j) (hf j)) l atTop := by
  have hn : ¬ Summable (fun n : ℤ => ‖φ.val.fst n‖^2) :=
    fun h => hφ ((mem_sourceHilbertLocus_iff h2p φ).mpr h)
  apply tendsto_atTop.mpr
  intro b
  have hex : ∃ S : Finset ℤ, b < ∑ n ∈ S, ‖φ.val.fst n‖^2 := by
    by_contra h
    push Not at h
    exact hn (summable_of_sum_le (fun _ => sq_nonneg _) h)
  obtain ⟨S,hS⟩ := hex
  have hc (n : ℤ) : Continuous (fun ξ : realTypeSourceSubmodule p => ξ.val.fst n) :=
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).continuous.comp
      ((CoeffPair.toMax p).continuous.fst.comp continuous_subtype_val)
  have ht : Tendsto (fun j => ∑ n ∈ S, ‖(ψ j).val.fst n‖^2) l
      (𝓝 (∑ n ∈ S, ‖φ.val.fst n‖^2)) :=
    tendsto_finsetSum S (fun n _ => ((hc n).continuousAt.tendsto.comp hψ).norm.pow 2)
  filter_upwards [ht.eventually (lt_mem_nhds hS)] with j hj
  exact hj.le.trans (sum_fst_sq_le_sourceFiniteGapRealMass hp hp1 (ψ j) (hf j) S)

/-- Such finite-gap approximations exist at every real source. -/
theorem exists_sourceFiniteGap_sequence (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p) :
    ∃ ψ : ℕ → realTypeSourceSubmodule p, (∀ j, ψ j ∈ sourceFiniteGapLocus hp hp1) ∧
      Tendsto ψ atTop (𝓝 φ) := by
  exact mem_closure_iff_seq_limit.mp (dense_sourceFiniteGapLocus hp hp1 φ)

end NLS.ZakharovShabat
