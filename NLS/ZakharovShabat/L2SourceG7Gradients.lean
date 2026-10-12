import NLS.ZakharovShabat.L2SourceDirichletFourier
import NLS.ZakharovShabat.SourceLemmaG7
import NLS.Fourier.IntervalCoefficientLinearity

/-! # G.7 coefficient estimates for actual normalized L2 root gradients

The Dirichlet error subtracts the actual zero-potential gradient. One common
complex source domain supports physical realization and the established
H1 summability estimate. The source exponents and Fourier signs are retained.
-/
noncomputable section
open Set Complex NLS.LinearVolterra NLS.Fourier
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Root gradients use the signed Fourier convention without G.6's factor i. -/
def L2RootGradientFourierRealizes {q : ℝ≥0∞} (g : ℝ → ℂ × ℂ) (a : CoeffPair q) : Prop :=
  ∀ k : ℤ, a.fst k = intervalFourierCoefficient 1 (fun s => (g s).1) (-k) ∧
    a.snd k = intervalFourierCoefficient 1 (fun s => (g s).2) k

/-- Actual coefficient integrals determine the represented vector uniquely. -/
theorem L2RootGradientFourierRealizes.unique {q : ℝ≥0∞} [Fact (1 ≤ q)]
    {g : ℝ → ℂ × ℂ} {a b : CoeffPair q} (ha : L2RootGradientFourierRealizes g a)
    (hb : L2RootGradientFourierRealizes g b) : a = b := by
  apply (CoeffPair.toMax q).injective
  apply Prod.ext
  · ext k
    exact (ha k).1.trans (hb k).1.symm
  · ext k
    exact (ha k).2.trans (hb k).2.symm

/-- The represented source vector has the exact combined finite-q coefficient energy. -/
theorem L2RootGradientFourierRealizes.norm_rpow {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : q ≠ ⊤)
    {g : ℝ → ℂ × ℂ} {a : CoeffPair q} (ha : L2RootGradientFourierRealizes g a) :
    ‖a‖^q.toReal = ∑' k : ℤ,
      (‖intervalFourierCoefficient 1 (fun s => (g s).1) (-k)‖^q.toReal+
       ‖intervalFourierCoefficient 1 (fun s => (g s).2) k‖^q.toReal) := by
  rw [CoeffPair.norm_rpow_eq_tsum hq]
  apply tsum_congr
  intro k
  rw [(ha k).1,(ha k).2]

/-- The physical error uses the exact free normalized L2 gradient. -/
def l2DirichletGradientRemainder (u : IntervalPairL2) (z w : ℂ) (s : ℝ) : ℂ × ℂ :=
  l2DirichletNormalizedGradient u z s-l2DirichletNormalizedGradient 0 w s

/-- The actual free reference has corrected signed frequencies and factor one half. -/
theorem l2DirichletGradientRemainder_lattice (u : IntervalPairL2) (z : ℂ) (n : ℤ)
    (s : Icc (0 : ℝ) 1) :
    l2DirichletGradientRemainder u z ((Real.pi : ℂ)*n) s =
      l2DirichletNormalizedGradient u z s-(1/2 : ℂ) • (wave (2*n) s,wave (-(2*n)) s) := by
  unfold l2DirichletGradientRemainder
  rw [← continuousPotentialL2Class_zero,l2DirichletNormalizedGradient_of_continuous,
    classicalDirichletNormalizedGradient_free_lattice]

variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [q.HolderConjugate p]

/-- At every included Hilbert source in one common complex domain, the
existing G.7 error vector realizes the actual normalized L2 gradient error. -/
theorem exists_global_sourceG7_l2_realization
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧
      ∀ φ : CoeffPair 2, CoeffPair.exponentInclusion h2p φ ∈ W → ∀ n : ℤ,
        let z := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet (CoeffPair.exponentInclusion h2p φ) n
        l2DirichletNormalization (sourcePhysicalL2 φ) z ≠ 0 ∧
          L2RootGradientFourierRealizes (l2DirichletGradientRemainder (sourcePhysicalL2 φ) z ((Real.pi : ℂ)*n))
            (sourceG7DirichletGradientError (q := q) hp hp1 (CoeffPair.exponentInclusion h2p φ) n) := by
  obtain ⟨W,hW,hreal,hgradient⟩ := exists_global_source_dirichlet_l2_fourier hp hp1 h2p
  refine ⟨W,hW,hreal,?_⟩
  have hzero : CoeffPair.exponentInclusion h2p (0 : CoeffPair 2) ∈ W := by
    simpa using hreal (show (0 : CoeffPair p) ∈ realTypeSourceLocus p by intro k; simp)
  have hcoeff (f : ℝ → ℂ) (k : ℤ) : intervalFourierCoefficient 1 f k = unitFourierCoefficient f k := by
    rw [intervalFourierCoefficient_eq_fourierCoeffOn (by norm_num),unitFourierCoefficient_eq_fourierCoeffOn]
  intro φ hφ n
  dsimp only
  obtain ⟨hQ,hd⟩ := hgradient φ hφ n
  refine ⟨hQ,fun k => ?_⟩
  have h0 := (hgradient 0 hzero n).2
  simp only [map_zero,canonicalPeriodOneBoundaryRoots_zero] at h0
  have hactual := continuous_l2DirichletNormalizedGradient (sourcePhysicalL2 φ)
    (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet (CoeffPair.exponentInclusion h2p φ) n)
  have hfree := continuous_l2DirichletNormalizedGradient 0 ((Real.pi : ℂ)*n)
  have hfst := (sourceDirichletConjugateGradientError_coefficients (q := q) hp hp1
    (CoeffPair.exponentInclusion h2p φ) n (-k)).1
  have hsnd := (sourceDirichletConjugateGradientError_coefficients (q := q) hp hp1
    (CoeffPair.exponentInclusion h2p φ) n k).2
  dsimp only at hfst hsnd
  simp only [neg_neg] at hfst
  rw [← fderiv_canonicalDirichletRoot_zero_eq_free hp hp1 h2p n,sub_apply,(hd k).1,(h0 k).1] at hfst
  rw [← fderiv_canonicalDirichletRoot_zero_eq_free hp hp1 h2p n,sub_apply,(hd (-k)).2,(h0 (-k)).2] at hsnd
  simp only [neg_neg] at hsnd
  constructor
  · change (sourceDirichletConjugateGradientError (q := q) hp hp1 (CoeffPair.exponentInclusion h2p φ) n).fst (-k) = _
    rw [hfst]
    change _ = intervalFourierCoefficient 1 (fun s =>
      (l2DirichletNormalizedGradient (sourcePhysicalL2 φ)
        (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet (CoeffPair.exponentInclusion h2p φ) n) s).1-
      (l2DirichletNormalizedGradient 0 ((Real.pi : ℂ)*n) s).1) (-k)
    rw [intervalFourierCoefficient_sub 1 _ _ hactual.fst hfree.fst,hcoeff,hcoeff]
  · change (sourceDirichletConjugateGradientError (q := q) hp hp1 (CoeffPair.exponentInclusion h2p φ) n).snd k = _
    rw [hsnd]
    change _ = intervalFourierCoefficient 1 (fun s =>
      (l2DirichletNormalizedGradient (sourcePhysicalL2 φ)
        (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet (CoeffPair.exponentInclusion h2p φ) n) s).2-
      (l2DirichletNormalizedGradient 0 ((Real.pi : ℂ)*n) s).2) k
    rw [intervalFourierCoefficient_sub 1 _ _ hactual.snd hfree.snd,hcoeff,hcoeff]

/-- The physical realization and corrected H1 G.7 estimates hold on the same
open complex domain, with every signed index and the exact original source norm. -/
theorem exists_global_sourceG7_l2_memlp
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧
      ∀ a : ScalarDomain 2 × ScalarDomain 2,
        CoeffPair.exponentInclusion h2p (sobolevSourceInclusion a) ∈ W →
        Memℓp (fun n : ℤ => sourceG7DirichletGradientError (q := q) hp hp1
          (CoeffPair.exponentInclusion h2p (sobolevSourceInclusion a)) n) p ∧
        ∀ n : ℤ,
          let φ := sobolevSourceInclusion a
          let z := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet (CoeffPair.exponentInclusion h2p φ) n
          l2DirichletNormalization (sourcePhysicalL2 φ) z ≠ 0 ∧
            L2RootGradientFourierRealizes (l2DirichletGradientRemainder (sourcePhysicalL2 φ) z ((Real.pi : ℂ)*n))
              (sourceG7DirichletGradientError (q := q) hp hp1 (CoeffPair.exponentInclusion h2p φ) n) := by
  obtain ⟨U,hU,hUr,hu⟩ := exists_global_sourceG7_l2_realization (q := q) hp hp1 h2p
  obtain ⟨V,hV,hVr,hv⟩ := sourceLemmaG7_corrected (q := q) hp hp1 h2p
  refine ⟨U ∩ V,hU.inter hV,fun φ hφ => ⟨hUr hφ,hVr hφ⟩,?_⟩
  intro a ha
  exact ⟨(hv a ha.2).2,fun n => hu _ ha.1 n⟩

/-- Every real H1 source has the realized G.7 sequence, with no additional
simplicity, normalization, or smallness premise. -/
theorem sourceG7_l2_memlp_real
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (a : ScalarDomain 2 × ScalarDomain 2) (ha : sobolevSourceInclusion a ∈ realTypeSourceLocus 2) :
    Memℓp (fun n : ℤ => sourceG7DirichletGradientError (q := q) hp hp1
      (CoeffPair.exponentInclusion h2p (sobolevSourceInclusion a)) n) p ∧ ∀ n : ℤ,
      let φ := sobolevSourceInclusion a
      let z := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet (CoeffPair.exponentInclusion h2p φ) n
      l2DirichletNormalization (sourcePhysicalL2 φ) z ≠ 0 ∧
        L2RootGradientFourierRealizes (l2DirichletGradientRemainder (sourcePhysicalL2 φ) z ((Real.pi : ℂ)*n))
          (sourceG7DirichletGradientError (q := q) hp hp1 (CoeffPair.exponentInclusion h2p φ) n) := by
  obtain ⟨W,_,hreal,h⟩ := exists_global_sourceG7_l2_memlp (q := q) hp hp1 h2p
  exact h a (hreal (fun n => ha n))

end NLS.ZakharovShabat
