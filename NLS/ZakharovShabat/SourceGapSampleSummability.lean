import NLS.ZakharovShabat.SourcePeriodicGapSummability
import NLS.ZakharovShabat.SourceGlobalIsolation
import NLS.ZakharovShabat.SourceStandardRootAlgebra
import NLS.ZakharovShabat.SourceStandardRootGapSideSource
import NLS.SequenceSpaces.SandwichMajorant

/-!
# Summability of arbitrary points selected from periodic gaps

For Lemma 12.7, choose one zero of the numerator variation in each
retained periodic gap. Every such sample differs from the free lattice
by an `ℓᵖ` sequence because the left endpoints and gap lengths already
have `ℓᵖ` displacements. The omitted index may be assigned any value.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

theorem norm_sourcePeriodicSegment_sample_sub_free_le
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (m : ℤ) (z : ℂ)
    (hz : z ∈ sourcePeriodicSegment hp hp1 ψ m) :
    ‖z-(Real.pi:ℂ)*m‖ ≤
      ‖(canonicalPeriodicLeftDisplacement hp hp1
        (periodOnePotential ψ) (periodOnePotential_mem ψ)) m‖ +
      ‖(sourcePeriodicGapDisplacement hp hp1 ψ) m‖ := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) m
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) m
  have hseg : z ∈ segment ℝ l r := hz
  have hzleft : ‖z-l‖ ≤ ‖r-l‖ := norm_sub_le_of_mem_segment hseg
  have hsplit : z-(Real.pi:ℂ)*m = (z-l)+(l-(Real.pi:ℂ)*m) := by ring
  rw [hsplit]
  have hbound := (norm_add_le (z-l) (l-(Real.pi:ℂ)*m)).trans
    (add_le_add_left hzleft _)
  simpa only [canonicalPeriodicLeftDisplacement_apply,
    sourcePeriodicGapDisplacement_apply, canonicalPeriodicGap,
    add_comm, l, r] using hbound

/-- Any modewise selection from the source's closed periodic gap
segments has an `ℓᵖ` displacement from the free lattice. -/
theorem memℓp_sourcePeriodicSegment_samples
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (ρ : ℤ → ℂ)
    (hρ : ∀ m : ℤ, ρ m ∈ sourcePeriodicSegment hp hp1 ψ m) :
    Memℓp (fun m => ρ m-(Real.pi:ℂ)*m) p := by
  let L := canonicalPeriodicLeftDisplacement hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ)
  let G := sourcePeriodicGapDisplacement hp hp1 ψ
  let A : Coeff p := Coeff.magnitude L + Coeff.magnitude G
  apply (lp.memℓp A).mono'
  intro m
  have hbound := norm_sourcePeriodicSegment_sample_sub_free_le
    hp hp1 ψ m (ρ m) (hρ m)
  have hA : ‖A m‖ = ‖L m‖+‖G m‖ := by
    simp only [A, lp.coeFn_add,Pi.add_apply,Coeff.magnitude_apply,
      ← Complex.ofReal_add,Complex.norm_real,
      Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  simpa only [L,G,hA] using hbound

/-- The selected samples may have an arbitrary value at one omitted
index without losing `ℓᵖ` summability. -/
theorem memℓp_sourcePeriodicSegment_samples_off_index
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) (ρ : ℤ → ℂ)
    (hρ : ∀ m : ℤ, m ≠ n →
      ρ m ∈ sourcePeriodicSegment hp hp1 ψ m) :
    Memℓp (fun m => ρ m-(Real.pi:ℂ)*m) p := by
  let ρ' : ℤ → ℂ := fun m =>
    if m = n then sourceStandardRootMidpoint hp hp1 ψ n else ρ m
  have hρ' : ∀ m : ℤ, ρ' m ∈ sourcePeriodicSegment hp hp1 ψ m := by
    intro m
    by_cases hm : m = n
    · subst m
      simpa only [ρ',↓reduceIte,sourceStandardRootMidpoint] using
        sourcePeriodicMidpoint_mem_segment hp hp1 ψ n
    · simpa only [ρ',if_neg hm] using hρ m hm
  let a : Coeff p :=
    ⟨fun m => ρ' m-(Real.pi:ℂ)*m,
      memℓp_sourcePeriodicSegment_samples hp hp1 ψ ρ' hρ'⟩
  let b : Coeff p := lp.single p n (ρ n-ρ' n)
  have hsum (m : ℤ) :
      ρ m-(Real.pi:ℂ)*m = (a+b) m := by
    change ρ m-(Real.pi:ℂ)*m =
      (ρ' m-(Real.pi:ℂ)*m) +
        (lp.single p n (ρ n-ρ' n) : Coeff p) m
    by_cases hm : m = n
    · subst m
      simp
    · rw [lp.single_apply_ne _ _ _ hm]
      simp [ρ',hm]
  have heq : (fun m => ρ m-(Real.pi:ℂ)*m) =
      (fun m => (a+b) m) := funext hsum
  rw [heq]
  exact lp.memℓp (a+b)

/-- The displaced sequence assembled from arbitrary retained-gap
samples, with one free index, as an actual `ℓᵖ` coefficient. -/
def sourceGapSampleDisplacement
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) (ρ : ℤ → ℂ)
    (hρ : ∀ m : ℤ, m ≠ n →
      ρ m ∈ sourcePeriodicSegment hp hp1 ψ m) : Coeff p :=
  ⟨fun m => ρ m-(Real.pi:ℂ)*m,
    memℓp_sourcePeriodicSegment_samples_off_index hp hp1 ψ n ρ hρ⟩

@[simp] theorem sourceGapSampleDisplacement_apply
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) (ρ : ℤ → ℂ)
    (hρ : ∀ m : ℤ, m ≠ n →
      ρ m ∈ sourcePeriodicSegment hp hp1 ψ m)
    (m : ℤ) :
    sourceGapSampleDisplacement hp hp1 ψ n ρ hρ m =
      ρ m-(Real.pi:ℂ)*m := rfl

end NLS.ZakharovShabat
