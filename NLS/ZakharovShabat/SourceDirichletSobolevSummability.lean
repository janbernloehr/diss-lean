import NLS.ZakharovShabat.SourceDirichletGradientErrorCotangent
import NLS.ZakharovShabat.SourceDirichletGradientFourierSummability
import NLS.ZakharovShabat.SourceFreeDirichletCotangent

/-! # Actual Dirichlet gradient summability on a common complex domain

The normalized physical Fourier error is identified with the genuine
canonical-root derivative minus the explicit free half-wave functional.
Both the Fourier coefficient pair and the actual source operator error
have full-sequence summability, including the finite central block.
-/

noncomputable section
open Set NLS.Fourier
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The genuine derivative error has a physical Fourier coefficient pair
whose ℓq norm forms an outer ℓˢ sequence, on one common complex domain. -/
theorem exists_global_source_dirichlet_gradient_error_memlp
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (s : ℝ) (hs : 1 < s) (q : ℝ≥0∞) (hq : ENNReal.ofReal (1+1/s) < q) :
    let hq1 : 1 < q := lt_of_le_of_lt
      (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity))) hq
    letI : Fact (1 ≤ q) := ⟨hq1.le⟩
    ∃ W : Set (CoeffPair p), IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧
      ∀ (φ : CoeffPair 2), CoeffPair.exponentInclusion h2p φ ∈ W →
      ∀ (a : Domain 2), periodOnePotential φ = domainInclusion a →
      ∃ G : ℤ → CoeffPair q, Memℓp G (ENNReal.ofReal s) ∧ ∀ n k : ℤ,
        let μ := fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n
        let L := fderiv ℂ μ (CoeffPair.exponentInclusion h2p φ)-sourceFreeDirichletCotangent p n
        L (CoeffPair.inlCLM (lp.single p k 1)) = (G n).fst (-k) ∧
        L (CoeffPair.inrCLM (lp.single p k 1)) = (G n).snd (-k) := by
  dsimp only
  have hq1 : 1 < q := lt_of_le_of_lt
    (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity))) hq
  let : Fact (1 ≤ q) := ⟨hq1.le⟩
  obtain ⟨W,hW,hreal,hcoeff⟩ := exists_global_source_dirichlet_fderiv_error_fourier hp hp1 h2p hq1
  refine ⟨W,hW,hreal,?_⟩
  intro φ hφ a ha
  let F (P : (ℂ × ℂ) →L[ℝ] ℂ) (n : ℤ) := classicalDirichletGradientFourierCoefficients hq1
    (classicalSobolevPotential a)
    (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet (CoeffPair.exponentInclusion h2p φ) n)
    ((Real.pi : ℂ)*n) P
  let G (n : ℤ) : CoeffPair q := CoeffPair.inlCLM (F (ContinuousLinearMap.fst ℝ ℂ ℂ) n)+
    CoeffPair.inrCLM (F (ContinuousLinearMap.snd ℝ ℂ ℂ) n)
  have h₁ := memlp_source_dirichlet_gradient_fourier_norms hp hp1 h2p s hs q hq φ a ha
    (ContinuousLinearMap.fst ℝ ℂ ℂ) (ContinuousLinearMap.norm_fst_le ..)
  have h₂ := memlp_source_dirichlet_gradient_fourier_norms hp hp1 h2p s hs q hq φ a ha
    (ContinuousLinearMap.snd ℝ ℂ ℂ) (ContinuousLinearMap.norm_snd_le ..)
  refine ⟨G,?_,?_⟩
  · apply (h₁.add h₂).mono
    intro n
    simpa only [G,F,Pi.add_apply,CoeffPair.norm_inlCLM,CoeffPair.norm_inrCLM] using
      norm_add_le (CoeffPair.inlCLM (p := q) (F (ContinuousLinearMap.fst ℝ ℂ ℂ) n))
        (CoeffPair.inrCLM (p := q) (F (ContinuousLinearMap.snd ℝ ℂ ℂ) n))
  intro n k
  have h := hcoeff φ hφ a ha n k
  dsimp only at h ⊢
  rw [fderiv_canonicalDirichletRoot_zero_eq_free hp hp1 h2p n] at h
  simpa [G,F] using h

/-- G.7's Dirichlet estimate in the literal conjugate Fourier pair norm:
the coefficient pair of the actual derivative error is an outer ℓp sequence. -/
theorem exists_global_source_dirichlet_conjugate_gradient_error_memlp
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p) :
    let q := ENNReal.ofReal (p.toReal/(p.toReal-1))
    letI : Fact (1 ≤ q) := ⟨ENNReal.one_le_ofReal.mpr (by
      have hs : 1 < p.toReal := (ENNReal.toReal_lt_toReal (by simp) hp).mpr hp1
      apply (le_div_iff₀ (by linarith : 0 < p.toReal-1)).mpr
      linarith)⟩
    ∃ W : Set (CoeffPair p), IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧
      ∀ (φ : CoeffPair 2), CoeffPair.exponentInclusion h2p φ ∈ W →
      ∀ (a : Domain 2), periodOnePotential φ = domainInclusion a →
      ∃ G : ℤ → CoeffPair q, Memℓp G p ∧ ∀ n k : ℤ,
        let μ := fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n
        let L := fderiv ℂ μ (CoeffPair.exponentInclusion h2p φ)-sourceFreeDirichletCotangent p n
        L (CoeffPair.inlCLM (lp.single p k 1)) = (G n).fst (-k) ∧
        L (CoeffPair.inrCLM (lp.single p k 1)) = (G n).snd (-k) := by
  have hs : 1 < p.toReal := (ENNReal.toReal_lt_toReal (by simp) hp).mpr hp1
  have h := exists_global_source_dirichlet_gradient_error_memlp hp hp1 h2p p.toReal hs _
    (conjugate_exponent_ennreal_gt_gradient_threshold p.toReal hs)
  simpa only [ENNReal.ofReal_toReal hp] using h

/-- The actual source operator errors form an outer ℓp sequence for every
finite source exponent p≥2 on a common neighborhood of all real sources. -/
theorem exists_global_source_dirichlet_fderiv_sobolev_memlp
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧
      ∀ (φ : CoeffPair 2), CoeffPair.exponentInclusion h2p φ ∈ W →
      ∀ (a : Domain 2), periodOnePotential φ = domainInclusion a →
      Memℓp (fun n : ℤ =>
        fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n)
          (CoeffPair.exponentInclusion h2p φ)-sourceFreeDirichletCotangent p n) p := by
  have hs : 1 < p.toReal := (ENNReal.toReal_lt_toReal (by simp) hp).mpr hp1
  let q := ENNReal.ofReal (p.toReal/(p.toReal-1))
  have hq : ENNReal.ofReal (1+1/p.toReal) < q :=
    conjugate_exponent_ennreal_gt_gradient_threshold p.toReal hs
  have hq1 : 1 < q := lt_of_le_of_lt
    (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity))) hq
  let : Fact (1 ≤ q) := ⟨hq1.le⟩
  let : q.HolderConjugate p := by
    have hc := (Real.HolderConjugate.conjExponent hs).symm.ennrealOfReal
    simpa only [Real.conjExponent,q,ENNReal.ofReal_toReal hp] using hc
  obtain ⟨W,hW,hreal,hbound⟩ := exists_global_source_dirichlet_fderiv_error_fourier_bound hp hp1 h2p hq1
  refine ⟨W,hW,hreal,?_⟩
  intro φ hφ a ha
  have h₁ := memlp_source_dirichlet_gradient_fourier_norms hp hp1 h2p p.toReal hs q hq φ a ha
    (ContinuousLinearMap.fst ℝ ℂ ℂ) (ContinuousLinearMap.norm_fst_le ..)
  have h₂ := memlp_source_dirichlet_gradient_fourier_norms hp hp1 h2p p.toReal hs q hq φ a ha
    (ContinuousLinearMap.snd ℝ ℂ ℂ) (ContinuousLinearMap.norm_snd_le ..)
  have hm : Memℓp (fun n : ℤ =>
      fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n)
        (CoeffPair.exponentInclusion h2p φ)-sourceFreeDirichletCotangent p n) (ENNReal.ofReal p.toReal) := by
    apply (h₁.add h₂).mono
    intro n
    have h := hbound φ hφ a ha n
    dsimp only at h
    rwa [fderiv_canonicalDirichletRoot_zero_eq_free hp hp1 h2p n] at h
  simpa only [ENNReal.ofReal_toReal hp] using hm

/-- Every real H¹ source satisfies the actual Dirichlet derivative estimate. -/
theorem memlp_real_source_dirichlet_fderiv_sobolev
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (φ : CoeffPair 2) (hφ : φ ∈ realTypeSourceLocus 2) (a : Domain 2)
    (ha : periodOnePotential φ = domainInclusion a) :
    Memℓp (fun n : ℤ =>
      fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n)
        (CoeffPair.exponentInclusion h2p φ)-sourceFreeDirichletCotangent p n) p := by
  obtain ⟨W,_,hreal,h⟩ := exists_global_source_dirichlet_fderiv_sobolev_memlp hp hp1 h2p
  exact h φ (hreal (fun n => hφ n)) a ha

end NLS.ZakharovShabat
