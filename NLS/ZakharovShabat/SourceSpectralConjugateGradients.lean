import NLS.SequenceSpaces.SourceConjugateGradient
import NLS.ZakharovShabat.SourceSpectralGradientSobolevSummability

/-! # G.7 in the conjugate Fourier pair norm

Both actual spectral derivative estimates are now expressed in the
physical conjugate Fourier coefficient space, with its component-sum norm.
The same open complex domain works for both sequences and every signed
index. Finite central blocks and collapsed periodic gaps are included.
-/

noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [q.HolderConjugate p]

/-- Physical conjugate Fourier coefficients of the actual midpoint derivative. -/
def sourceMidpointConjugateGradient (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) (n : ℤ) : CoeffPair q :=
  CoeffPair.conjugateGradient hp ((ENNReal.HolderConjugate.ne_top_iff_ne_one q p).mpr hp1.ne')
    (fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodicMidpoint hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) n) φ)

/-- Physical conjugate Fourier coefficients of the actual Dirichlet
derivative after subtracting the exact free half-wave functional. -/
def sourceDirichletConjugateGradientError (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) (n : ℤ) : CoeffPair q :=
  CoeffPair.conjugateGradient hp ((ENNReal.HolderConjugate.ne_top_iff_ne_one q p).mpr hp1.ne')
    (fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n) φ-
      sourceFreeDirichletCotangent p n)

/-- The two midpoint components use the physical, reversed-frequency convention. -/
theorem sourceMidpointConjugateGradient_coefficients (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (n k : ℤ) :
    let L := fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodicMidpoint hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) n) φ
    (sourceMidpointConjugateGradient (q := q) hp hp1 φ n).fst k = L (CoeffPair.inlCLM (lp.single p (-k) 1)) ∧
    (sourceMidpointConjugateGradient (q := q) hp hp1 φ n).snd k = L (CoeffPair.inrCLM (lp.single p (-k) 1)) := by
  simp [sourceMidpointConjugateGradient]

/-- The Dirichlet error components recover the genuine derivative minus
the free functional, with the same physical index reversal. -/
theorem sourceDirichletConjugateGradientError_coefficients (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (n k : ℤ) :
    let L := fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n) φ-
      sourceFreeDirichletCotangent p n
    (sourceDirichletConjugateGradientError (q := q) hp hp1 φ n).fst k = L (CoeffPair.inlCLM (lp.single p (-k) 1)) ∧
    (sourceDirichletConjugateGradientError (q := q) hp hp1 φ n).snd k = L (CoeffPair.inrCLM (lp.single p (-k) 1)) := by
  simp [sourceDirichletConjugateGradientError]

/-- The midpoint coefficient pair represents the entire source derivative,
not only its finite unit-mode values. -/
theorem sourceMidpointConjugateGradient_dualPairing (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ h : CoeffPair p) (n : ℤ) :
    Coeff.dualPairing (Coeff.reflection (sourceMidpointConjugateGradient (q := q) hp hp1 φ n).fst) h.fst+
      Coeff.dualPairing (Coeff.reflection (sourceMidpointConjugateGradient (q := q) hp hp1 φ n).snd) h.snd =
        (fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodicMidpoint hp hp1
          (periodOnePotential ψ) (periodOnePotential_mem ψ) n) φ) h :=
  CoeffPair.dualPairing_conjugateGradient hp _ _ h

/-- The Dirichlet error coefficient pair represents the full derivative
error in every source direction, with the exact free correction. -/
theorem sourceDirichletConjugateGradientError_dualPairing (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ h : CoeffPair p) (n : ℤ) :
    Coeff.dualPairing (Coeff.reflection (sourceDirichletConjugateGradientError (q := q) hp hp1 φ n).fst) h.fst+
      Coeff.dualPairing (Coeff.reflection (sourceDirichletConjugateGradientError (q := q) hp hp1 φ n).snd) h.snd =
        (fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n) φ) h-
          (1/2 : ℂ)*(h.fst (-n)+h.snd n) :=
  CoeffPair.dualPairing_conjugateGradient hp _ _ h

/-- Both assertions of G.7 hold in the actual conjugate Fourier pair norm
for finite source exponents p≥2, on one common complex neighborhood. -/
theorem exists_global_source_spectral_gradients_conjugate_memlp
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧
      ∀ (φ : CoeffPair 2), CoeffPair.exponentInclusion h2p φ ∈ W →
      ∀ (a : Domain 2), periodOnePotential φ = domainInclusion a →
      Memℓp (fun n : ℤ => sourceMidpointConjugateGradient (q := q) hp hp1
        (CoeffPair.exponentInclusion h2p φ) n) p ∧
      Memℓp (fun n : ℤ => sourceDirichletConjugateGradientError (q := q) hp hp1
        (CoeffPair.exponentInclusion h2p φ) n) p := by
  obtain ⟨W,hW,hreal,hbound⟩ := exists_global_source_spectral_gradients_sobolev_memlp hp hp1 h2p
  refine ⟨W,hW,hreal,?_⟩
  intro φ hφ a ha
  obtain ⟨hmid,hdir⟩ := hbound φ hφ a ha
  exact ⟨CoeffPair.memlp_conjugateGradient hp _ _ hmid,CoeffPair.memlp_conjugateGradient hp _ _ hdir⟩

/-- In particular, every real H¹ source satisfies both conjugate Fourier estimates. -/
theorem memlp_real_source_spectral_gradients_conjugate
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (φ : CoeffPair 2) (hφ : φ ∈ realTypeSourceLocus 2) (a : Domain 2)
    (ha : periodOnePotential φ = domainInclusion a) :
    Memℓp (fun n : ℤ => sourceMidpointConjugateGradient (q := q) hp hp1
      (CoeffPair.exponentInclusion h2p φ) n) p ∧
    Memℓp (fun n : ℤ => sourceDirichletConjugateGradientError (q := q) hp hp1
      (CoeffPair.exponentInclusion h2p φ) n) p := by
  obtain ⟨W,_,hreal,h⟩ := exists_global_source_spectral_gradients_conjugate_memlp (q := q) hp hp1 h2p
  exact h φ (hreal (fun n => hφ n)) a ha

end NLS.ZakharovShabat
