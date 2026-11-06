import NLS.ZakharovShabat.EvenDiscriminantPeriodicEndpoints
import NLS.ZakharovShabat.SourceCanonicalRootProduct

/-! # Oddness of the actual canonical root for an even discriminant

The complete canonical endpoint reflection identifies the literal standard
root factors. Symmetric finite products, with the exceptional denominator
at zero retained, then prove oddness of the actual canonical root.
-/
noncomputable section
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem normalizedStandardRoot_neg_parameters (t g z : ℂ) :
    normalizedStandardRoot t g (-z) = -normalizedStandardRoot (-t) g z := by
  unfold normalizedStandardRoot
  rw [show -t-z = -(t- -z) by ring,neg_sq]
  ring

theorem neg_mem_complex_segment_iff (a b z : ℂ) :
    -z ∈ segment ℝ a b ↔ z ∈ segment ℝ (-b) (-a) := by
  rw [segment_symm ℝ (-b) (-a)]
  constructor
  · rintro ⟨s,t,hs,ht,hst,he⟩
    refine ⟨s,t,hs,ht,hst,?_⟩
    simpa only [smul_neg,← neg_add,neg_neg] using congrArg Neg.neg he
  · rintro ⟨s,t,hs,ht,hst,he⟩
    refine ⟨s,t,hs,ht,hst,?_⟩
    simpa only [smul_neg,← neg_add,neg_neg] using congrArg Neg.neg he

variable (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
  (heven : ∀ z, canonicalDiscriminant hp (periodOnePotential ψ) (-z) =
    canonicalDiscriminant hp (periodOnePotential ψ) z)
include heven

theorem sourcePeriodicMidpoint_neg_of_discriminant_even (n : ℤ) :
    canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) (-n) =
      -canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n := by
  obtain ⟨hl,hr⟩ := canonicalPeriodicEndpoints_neg_of_discriminant_even hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) heven n
  simp only [canonicalPeriodicMidpoint,hl,hr]
  ring

theorem sourcePeriodicGap_neg_of_discriminant_even (n : ℤ) :
    canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) (-n) =
      canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n := by
  obtain ⟨hl,hr⟩ := canonicalPeriodicEndpoints_neg_of_discriminant_even hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) heven n
  simp only [canonicalPeriodicGap,hl,hr]
  ring

theorem neg_mem_sourcePeriodicSegment_iff_of_discriminant_even (n : ℤ) (z : ℂ) :
    -z ∈ sourcePeriodicSegment hp hp1 ψ n ↔ z ∈ sourcePeriodicSegment hp hp1 ψ (-n) := by
  obtain ⟨hl,hr⟩ := canonicalPeriodicEndpoints_neg_of_discriminant_even hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) heven n
  simp only [sourcePeriodicSegment,hl,hr,neg_mem_complex_segment_iff]

theorem neg_mem_sourceCanonicalRootDomain_iff_of_discriminant_even (z : ℂ) :
    -z ∈ sourceCanonicalRootDomain hp hp1 ψ ↔ z ∈ sourceCanonicalRootDomain hp hp1 ψ := by
  constructor
  · intro h n
    have hn := h (-n)
    simpa only [neg_mem_sourcePeriodicSegment_iff_of_discriminant_even hp hp1 ψ heven,
      neg_neg] using hn
  · intro h n
    exact fun hz => h (-n)
      ((neg_mem_sourcePeriodicSegment_iff_of_discriminant_even hp hp1 ψ heven n z).mp hz)

theorem sourceStandardRoot_neg_of_discriminant_even (n : ℤ) (z : ℂ) :
    sourceStandardRoot hp hp1 ψ n (-z) = -sourceStandardRoot hp hp1 ψ (-n) z := by
  simp only [sourceStandardRoot,sourcePeriodicMidpoint_neg_of_discriminant_even hp hp1 ψ heven,
    sourcePeriodicGap_neg_of_discriminant_even hp hp1 ψ heven]
  exact normalizedStandardRoot_neg_parameters _ _ _

theorem sourceCanonicalRootPartialProduct_neg_of_discriminant_even (N : ℕ) (z : ℂ) :
    sourceCanonicalRootPartialProduct hp hp1 N ψ (-z) =
      -sourceCanonicalRootPartialProduct hp hp1 N ψ z := by
  let S := Finset.Icc (-(N : ℤ)) N
  let f : ℤ → ℂ → ℂ := fun n w => sourceStandardRoot hp hp1 ψ n w / singleSpectralDenominator n
  have h0 : (0 : ℤ) ∈ S := by simp [S]
  have hcentral : f 0 (-z) = -f 0 z := by
    simp [f,sourceStandardRoot_neg_of_discriminant_even hp hp1 ψ heven,
      singleSpectralDenominator]
  have hfar (n : ℤ) (hn : n ≠ 0) : f n (-z) = f (-n) z := by
    simp only [f,sourceStandardRoot_neg_of_discriminant_even hp hp1 ψ heven,
      singleSpectralDenominator,if_neg hn,if_neg (neg_ne_zero.mpr hn),Int.cast_neg,mul_neg,
      div_neg,neg_div]
  have hprod : (∏ n ∈ S.erase 0, f n (-z)) = ∏ n ∈ S.erase 0, f n z := by
    apply Finset.prod_bij (fun n _ => -n)
    · intro n hn
      simp only [Finset.mem_erase,Finset.mem_Icc,S] at hn ⊢
      constructor
      · exact neg_ne_zero.mpr hn.1
      · omega
    · intro n _ m _ hnm
      exact neg_injective hnm
    · intro n hn
      refine ⟨-n,?_,by simp⟩
      simpa only [Finset.mem_erase,Finset.mem_Icc,S,neg_ne_zero] using
        And.intro (Finset.mem_erase.mp hn).1 (by
          have hm := (Finset.mem_erase.mp hn).2
          simp only [S,Finset.mem_Icc] at hm
          omega)
    · intro n hn
      exact hfar n (Finset.mem_erase.mp hn).1
  change 2*I*(∏ n ∈ S, f n (-z)) = -(2*I*(∏ n ∈ S, f n z))
  rw [← Finset.mul_prod_erase S (fun n => f n (-z)) h0,
    ← Finset.mul_prod_erase S (fun n => f n z) h0,hcentral,hprod]
  ring

theorem sourceCanonicalRoot_neg_of_discriminant_even (z : ℂ) :
    sourceCanonicalRoot hp hp1 ψ (-z) = -sourceCanonicalRoot hp hp1 ψ z := by
  apply tendsto_nhds_unique (tendsto_sourceCanonicalRootPartialProduct hp hp1 ψ (-z))
  exact ((tendsto_sourceCanonicalRootPartialProduct hp hp1 ψ z).neg).congr'
    (Eventually.of_forall (fun N =>
      (sourceCanonicalRootPartialProduct_neg_of_discriminant_even hp hp1 ψ heven N z).symm))

end NLS.ZakharovShabat
