import NLS.ZakharovShabat.SourcePeriodicMidpointRefined
import NLS.ZakharovShabat.SourceLemma10_8Estimates

/-!
# The refined free-sine consequence of Lemma 10.8

The actual free numerator has a locally uniformly bounded midpoint
offset at every refined exponent. Hence its literal disk supremum has
one ℓ(p/2)+ℓ(1+) decomposition on the original source topology. This
settles the free-numerator consequence independently of the separate
failure of the printed uniformity claim for arbitrary numerators.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual filled free-sine quotient on every disk, with one fixed pair
of summands and locally uniform bounds for all ℓ(1+) projections. -/
def SourceFreeSineSupDecomposition (hp : p ≠ ⊤) (hp1 : 1 < p)
    (D : ℤ → Set ℂ) (V : Set (CoeffPair p)) : Prop :=
  ∃ A : CoeffPair p → Coeff (p/2), ∃ B : CoeffPair p → CoeffOnePlus,
    (∀ ψ ∈ V, ∀ n : ℤ,
      ((sSup ((fun z => ‖freeSineQuotient n z /
        sourceStandardRootOmittedJointProduct hp hp1 n (z,ψ)-1‖) '' D n) : ℝ):ℂ) = A ψ n+(B ψ).1 n) ∧
    (∃ K : ℝ, 0 ≤ K ∧ ∀ ψ ∈ V, ‖A ψ‖ ≤ K) ∧
    ∀ (r : ℝ≥0∞) (hr1 : 1 < r) (hr : r ≠ ⊤),
      ∃ K : ℝ, 0 ≤ K ∧ ∀ ψ ∈ V, ‖CoeffOnePlus.toCoeff r hr1 hr (B ψ)‖ ≤ K

/-- Every existing original disk family admits the refined free-numerator estimate. -/
theorem SourceQuotientDiscEstimates.freeSineSupDecomposition_refined
    {hp : p ≠ ⊤} {hp1 : 1 < p} {U : Set (Coeff p × CoeffPair p)}
    {D : ℤ → Set ℂ} {c R H M : ℝ} {N K : ℕ}
    (h : SourceQuotientDiscEstimates hp hp1 U D c R H M N K)
    (hU : IsOpen U) (φ : CoeffPair p) (hφ : (0,φ) ∈ U) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      (∀ ψ ∈ V, (0,ψ) ∈ U) ∧ SourceFreeSineSupDecomposition hp hp1 D V := by
  obtain ⟨V₀,ho,hφ₀,hmid⟩ := exists_uniform_sourcePeriodicMidpoint_refined hp hp1 φ
  let V := V₀ ∩ (fun ψ : CoeffPair p => ((0:Coeff p),ψ)) ⁻¹' U
  have hV : IsOpen V := ho.inter (hU.preimage (continuous_const.prodMk continuous_id))
  refine ⟨V,hV,⟨hφ₀,hφ⟩,fun ψ hψ => hψ.2,?_⟩
  have hb (r : ℝ≥0∞) (hr : r ≠ ⊤) (hr1 : 1 < r) (hpr : p/2 ≤ r) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ ∈ V, ∃ b : Coeff r,
        (∀ n, b n = (sourceQuotientDiscSup hp hp1 D (0,ψ) n : ℂ)) ∧ ‖b‖ ≤ C := by
    let : Fact (1 ≤ r) := ⟨hr1.le⟩
    obtain ⟨T,hT,ht⟩ := hmid r hr1 hr hpr
    obtain ⟨Lr,Lg,hLr,hLg,hbound⟩ := h.majorants hr1 hr T hT
    refine ⟨Lr+Lg,add_nonneg hLr hLg,?_⟩
    intro ψ hψ
    obtain ⟨E,hE,hEn⟩ := ht ψ hψ.1
    have hoff (m : ℤ) : displacedRoots (0:Coeff p) m-
        canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m = (-E) m := by
      simp only [lp.coeFn_neg,Pi.neg_apply,hE,sourcePeriodicMidpointDisplacement_apply,
        displacedRoots,lp.coeFn_zero,Pi.zero_apply,add_zero]
      ring
    obtain ⟨A,B,hA,hB,hpoint⟩ := hbound (0,ψ) hψ.2 (-E) (by simpa only [norm_neg] using hEn) hoff
    have hhalf : 0 < ENNReal.ofReal (p.toReal/2) := by
      rw [Coeff.halfExponent_eq_div hp]
      exact ENNReal.div_pos (zero_lt_one.trans hp1).ne' (by norm_num)
    obtain ⟨C,hC,hCn,_⟩ := Coeff.exists_tailCoeff_of_twoSequenceMajorants hhalf hr1 hr
      (by rwa [Coeff.halfExponent_eq_div hp])
      (fun n => (sourceQuotientDiscSup hp hp1 D (0,ψ) n : ℂ)) 0 A B (by
        intro n _
        rw [Complex.norm_real,Real.norm_of_nonneg (h.sup_nonneg (0,ψ) hψ.2 n)]
        exact h.sup_le (0,ψ) n _ (hpoint n))
    exact ⟨C,fun n => by simpa using hC n,hCn.trans (add_le_add hA hB)⟩
  obtain ⟨A,B,he,hA,hB⟩ := Coeff.exists_onePlus_decomposition_of_refined V
    (fun ψ n => (sourceQuotientDiscSup hp hp1 D (0,ψ) n : ℂ))
    (ENNReal.div_ne_top hp (by norm_num)) hb
  exact ⟨A,B,fun ψ hψ n => by simpa only [sourceQuotientDiscSup_free_eq] using he ψ hψ n,hA,hB⟩

/-- On the same almost-real source domain, the original isolating disks are
chosen before the refined free-sine neighborhood and all target exponents. -/
theorem SourceLemma10_8Estimates.freeSine_refined
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (h : SourceLemma10_8Estimates hp hp1 W) (φ : CoeffPair p) (hφ : φ ∈ W) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ IsConnected V ∧ φ ∈ V ∧ V ⊆ W ∧
      ∃ D c, SourceCanonicalRootNeighborhoods hp hp1 V D c ∧
        ∃ S : Set (CoeffPair p), IsOpen S ∧ φ ∈ S ∧ S ⊆ V ∧ SourceFreeSineSupDecomposition hp hp1 D S := by
  obtain ⟨V,ho,hc,hφV,hVW,D,c,hD,hnum⟩ := h.neighborhoods φ hφ
  obtain ⟨U,hU,hφU,hUV,R,H,M,N,K,hE⟩ := hnum 0
  obtain ⟨S,hS,hφS,hSU,hSbound⟩ := hE.freeSineSupDecomposition_refined hU φ hφU
  exact ⟨V,ho,hc,hφV,hVW,D,c,hD,S,hS,hφS,fun ψ hψ => (hUV (hSU ψ hψ)).2,hSbound⟩

/-- The refined free-sine consequence holds on one open connected neighborhood
of the whole real-type source locus, with every original isolating disk included. -/
theorem sourceLemma10_8_freeSine_refined (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ IsConnected W ∧ realTypeSourceLocus p ⊆ W ∧
      SourceLemma10_8Estimates hp hp1 W ∧
      ∀ φ ∈ W, ∃ V : Set (CoeffPair p), IsOpen V ∧ IsConnected V ∧ φ ∈ V ∧ V ⊆ W ∧
        ∃ D c, SourceCanonicalRootNeighborhoods hp hp1 V D c ∧
          ∃ S : Set (CoeffPair p), IsOpen S ∧ φ ∈ S ∧ S ⊆ V ∧ SourceFreeSineSupDecomposition hp hp1 D S := by
  obtain ⟨W,ho,hc,hr,h⟩ := sourceLemma10_8_estimates hp hp1
  exact ⟨W,ho,hc,hr,h,h.freeSine_refined⟩

end NLS.ZakharovShabat
