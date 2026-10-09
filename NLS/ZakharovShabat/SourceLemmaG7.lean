import NLS.ZakharovShabat.SourceLemmaG7ReferenceAudit
import NLS.ZakharovShabat.SourceSpectralConjugateGradients
import NLS.ZakharovShabat.SourceLemmaG3

/-! # G.7 in the original H¹ source and exact signed Fourier pair norm

The midpoint assertion is unchanged. The Dirichlet reference has the
corrected subscripts -2*n. A common open complex domain contains the
entire real source locus; no simplicity premise is imposed separately.
-/
noncomputable section
open Set NLS.Fourier
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Reversing the first physical index gives the source's signed wave convention. -/
def sourceG7SignedCoordinates (q : ℝ≥0∞) [Fact (1 ≤ q)] : CoeffPair q →ₗᵢ[ℂ] CoeffPair q :=
  Coeff.reflection.toLinearIsometry.withLpProdMap q (LinearIsometry.id : Coeff q →ₗᵢ[ℂ] Coeff q)

@[simp] theorem sourceG7SignedCoordinates_fst {q : ℝ≥0∞} [Fact (1 ≤ q)] (u : CoeffPair q) (k : ℤ) :
    (sourceG7SignedCoordinates q u).fst k = u.fst (-k) := rfl

@[simp] theorem sourceG7SignedCoordinates_snd {q : ℝ≥0∞} [Fact (1 ≤ q)] (u : CoeffPair q) (k : ℤ) :
    (sourceG7SignedCoordinates q u).snd k = u.snd k := rfl

/-- The signed convention preserves the exact finite-exponent pair norm. -/
@[simp] theorem norm_sourceG7SignedCoordinates {q : ℝ≥0∞} [Fact (1 ≤ q)] (u : CoeffPair q) :
    ‖sourceG7SignedCoordinates q u‖ = ‖u‖ := (sourceG7SignedCoordinates q).norm_map u

variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [q.HolderConjugate p]

/-- The actual midpoint derivative in the signed source coefficient convention. -/
def sourceG7MidpointGradient (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) (n : ℤ) : CoeffPair q :=
  sourceG7SignedCoordinates q (sourceMidpointConjugateGradient hp hp1 φ n)

/-- The actual Dirichlet derivative minus its exact free derivative, in signed source coordinates. -/
def sourceG7DirichletGradientError (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) (n : ℤ) : CoeffPair q :=
  sourceG7SignedCoordinates q (sourceDirichletConjugateGradientError hp hp1 φ n)

/-- The two signed components recover the actual midpoint derivative on Fourier directions. -/
theorem sourceG7MidpointGradient_coefficients (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (n k : ℤ) :
    let L := fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodicMidpoint hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) n) φ
    (sourceG7MidpointGradient (q := q) hp hp1 φ n).fst k = L (CoeffPair.inlCLM (lp.single p k 1)) ∧
    (sourceG7MidpointGradient (q := q) hp hp1 φ n).snd k = L (CoeffPair.inrCLM (lp.single p (-k) 1)) := by
  simp [sourceG7MidpointGradient,sourceMidpointConjugateGradient]

/-- The corrected half waves have exactly one half in both signed components at mode -n. -/
theorem sourceG7_free_signed_coefficients (hp : p ≠ ⊤) (hp1 : 1 < p) (n k : ℤ) :
    let g := sourceG7SignedCoordinates q (CoeffPair.conjugateGradient hp
      ((ENNReal.HolderConjugate.ne_top_iff_ne_one q p).mpr hp1.ne') (sourceFreeDirichletCotangent p n))
    g.fst k = (if k = -n then (1/2 : ℂ) else 0) ∧
    g.snd k = (if k = -n then (1/2 : ℂ) else 0) := by
  simp only [sourceG7SignedCoordinates_fst,sourceG7SignedCoordinates_snd,
    CoeffPair.conjugateGradient_fst,CoeffPair.conjugateGradient_snd,neg_neg,
    sourceFreeDirichletCotangent_apply]
  by_cases hk : k = -n
  · subst k
    simp
  · have hn : n ≠ -k := by omega
    simp [lp.single_apply,hk,Ne.symm hk,hn]

/-- Every original H¹ source supplies its physical Sobolev representative without an extra premise. -/
theorem sourceG7_periodic_representative (a : ScalarDomain 2 × ScalarDomain 2) :
    periodOnePotential (sobolevSourceInclusion a) = domainInclusion (sourceG3ClassicalCoefficients a) := by
  apply Prod.ext <;> ext n <;>
    simp [periodOnePotential_apply,domainInclusion_apply,sourceG3ClassicalCoefficients,
      scalarInclusion_apply,Coeff.periodDoubleSobolev_apply,sobolevSourceInclusion]

/-- Both finite-exponent G.7 estimates in the exact signed pair norm on one common complex domain. -/
theorem sourceLemmaG7_corrected
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧
      ∀ a : ScalarDomain 2 × ScalarDomain 2,
        CoeffPair.exponentInclusion h2p (sobolevSourceInclusion a) ∈ W →
        Memℓp (fun n : ℤ => sourceG7MidpointGradient (q := q) hp hp1
          (CoeffPair.exponentInclusion h2p (sobolevSourceInclusion a)) n) p ∧
        Memℓp (fun n : ℤ => sourceG7DirichletGradientError (q := q) hp hp1
          (CoeffPair.exponentInclusion h2p (sobolevSourceInclusion a)) n) p := by
  obtain ⟨W,hW,hreal,h⟩ := exists_global_source_spectral_gradients_conjugate_memlp (q := q) hp hp1 h2p
  refine ⟨W,hW,hreal,?_⟩
  intro a ha
  obtain ⟨hm,hd⟩ := h (sobolevSourceInclusion a) ha (sourceG3ClassicalCoefficients a)
    (sourceG7_periodic_representative a)
  constructor
  · apply Memℓp.of_norm
    simpa only [sourceG7MidpointGradient,norm_sourceG7SignedCoordinates] using hm.norm
  · apply Memℓp.of_norm
    simpa only [sourceG7DirichletGradientError,norm_sourceG7SignedCoordinates] using hd.norm

/-- In particular both estimates hold at every real H¹ source, with no smallness assumption. -/
theorem sourceLemmaG7_real_corrected
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (a : ScalarDomain 2 × ScalarDomain 2) (ha : sobolevSourceInclusion a ∈ realTypeSourceLocus 2) :
    Memℓp (fun n : ℤ => sourceG7MidpointGradient (q := q) hp hp1
      (CoeffPair.exponentInclusion h2p (sobolevSourceInclusion a)) n) p ∧
    Memℓp (fun n : ℤ => sourceG7DirichletGradientError (q := q) hp hp1
      (CoeffPair.exponentInclusion h2p (sobolevSourceInclusion a)) n) p := by
  obtain ⟨W,_,hreal,h⟩ := sourceLemmaG7_corrected (q := q) hp hp1 h2p
  exact h a (hreal (fun n => ha n))

/-- At zero, subtracting the actual free derivative cancels exactly at every exponent. -/
@[simp] theorem sourceG7DirichletGradientError_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p) (n : ℤ) :
    sourceG7DirichletGradientError (q := q) hp hp1 0 n = 0 := by
  apply (CoeffPair.toMax q).injective
  apply Prod.ext <;> ext k <;>
    simp [sourceG7DirichletGradientError,sourceDirichletConjugateGradientError,
      fderiv_canonicalDirichletRoot_zero_eq_free hp hp1 h2p n]

/-- The literal corrected physical remainder: normalized gradient minus the half waves. -/
def sourceG7CorrectedDirichletError (φ : NLS.LinearVolterra.Curve (ℂ × ℂ)) (z : ℂ)
    (n : ℤ) (t : ℝ) : ℂ × ℂ :=
  classicalDirichletNormalizedGradient φ z t-(1/2 : ℂ) • (wave (2*n) t,wave (-(2*n)) t)

/-- The source coordinate identification records both actual Fourier integrals. -/
def SourceG7DirichletCoefficients (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (a : ScalarDomain 2 × ScalarDomain 2) : Prop :=
  ∀ n k : ℤ,
    let φ := CoeffPair.exponentInclusion h2p (sobolevSourceInclusion a)
    let z := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ n
    let g := sourceG7CorrectedDirichletError (classicalSobolevPotential (sourceG3ClassicalCoefficients a)) z n
    (sourceG7DirichletGradientError (q := q) hp hp1 φ n).fst k =
      intervalFourierCoefficient 1 (fun t => (g t).1) (-k) ∧
    (sourceG7DirichletGradientError (q := q) hp hp1 φ n).snd k =
      intervalFourierCoefficient 1 (fun t => (g t).2) k

/-- One complex neighborhood identifies the actual derivative error with the corrected reference. -/
theorem exists_sourceG7_dirichlet_coefficients
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧
      ∀ a : ScalarDomain 2 × ScalarDomain 2,
        CoeffPair.exponentInclusion h2p (sobolevSourceInclusion a) ∈ W →
        SourceG7DirichletCoefficients (q := q) hp hp1 h2p a := by
  obtain ⟨W,hW,hreal,h⟩ := exists_global_source_dirichlet_fderiv_error_fourier hp hp1 h2p
    (q := 2) (by norm_num)
  refine ⟨W,hW,hreal,?_⟩
  intro a ha n k
  dsimp only
  have hfst := (h (sobolevSourceInclusion a) ha (sourceG3ClassicalCoefficients a)
    (sourceG7_periodic_representative a) n k).1
  have hsnd := (h (sobolevSourceInclusion a) ha (sourceG3ClassicalCoefficients a)
    (sourceG7_periodic_representative a) n (-k)).2
  dsimp only at hfst hsnd
  rw [fderiv_canonicalDirichletRoot_zero_eq_free hp hp1 h2p n] at hfst hsnd
  constructor
  · simp only [sourceG7DirichletGradientError,sourceG7SignedCoordinates_fst,
      sourceDirichletConjugateGradientError,CoeffPair.conjugateGradient_fst,neg_neg]
    rw [hfst,classicalDirichletGradientFourierCoefficients_apply]
    apply intervalFourierCoefficient_congr 1
    intro t ht
    dsimp only
    rw [classicalDirichletNormalizedGradient_free_lattice n ⟨t,by simpa using ht⟩]
    rfl
  · simp only [sourceG7DirichletGradientError,sourceG7SignedCoordinates_snd,
      sourceDirichletConjugateGradientError,CoeffPair.conjugateGradient_snd]
    rw [hsnd,classicalDirichletGradientFourierCoefficients_apply,neg_neg]
    apply intervalFourierCoefficient_congr 1
    intro t ht
    dsimp only
    rw [classicalDirichletNormalizedGradient_free_lattice n ⟨t,by simpa using ht⟩]
    rfl

/-- The corrected estimates and their actual half-wave integrals hold on the same source domain. -/
theorem sourceLemmaG7_corrected_with_coefficients
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧
      ∀ a : ScalarDomain 2 × ScalarDomain 2,
        CoeffPair.exponentInclusion h2p (sobolevSourceInclusion a) ∈ W →
        Memℓp (fun n : ℤ => sourceG7MidpointGradient (q := q) hp hp1
          (CoeffPair.exponentInclusion h2p (sobolevSourceInclusion a)) n) p ∧
        Memℓp (fun n : ℤ => sourceG7DirichletGradientError (q := q) hp hp1
          (CoeffPair.exponentInclusion h2p (sobolevSourceInclusion a)) n) p ∧
        SourceG7DirichletCoefficients (q := q) hp hp1 h2p a := by
  obtain ⟨U,hU,hrU,h⟩ := sourceLemmaG7_corrected (q := q) hp hp1 h2p
  obtain ⟨V,hV,hrV,hc⟩ := exists_sourceG7_dirichlet_coefficients (q := q) hp hp1 h2p
  exact ⟨U ∩ V,hU.inter hV,fun φ hφ => ⟨hrU hφ,hrV hφ⟩,
    fun a ha => ⟨(h a ha.1).1,(h a ha.1).2,hc a ha.2⟩⟩

/-- The norm is exactly the source's combined finite-q Fourier energy of the corrected error. -/
theorem sourceG7DirichletGradientError_norm_rpow
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p) (hq : q ≠ ⊤)
    (a : ScalarDomain 2 × ScalarDomain 2)
    (ha : SourceG7DirichletCoefficients (q := q) hp hp1 h2p a) (n : ℤ) :
    let φ := CoeffPair.exponentInclusion h2p (sobolevSourceInclusion a)
    let z := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ n
    let g := sourceG7CorrectedDirichletError (classicalSobolevPotential (sourceG3ClassicalCoefficients a)) z n
    ‖sourceG7DirichletGradientError (q := q) hp hp1 φ n‖^q.toReal =
      ∑' k : ℤ, (‖intervalFourierCoefficient 1 (fun t => (g t).1) (-k)‖^q.toReal+
        ‖intervalFourierCoefficient 1 (fun t => (g t).2) k‖^q.toReal) := by
  dsimp only
  rw [CoeffPair.norm_rpow_eq_tsum hq]
  apply tsum_congr
  intro k
  rw [(ha n k).1,(ha n k).2]

end NLS.ZakharovShabat
