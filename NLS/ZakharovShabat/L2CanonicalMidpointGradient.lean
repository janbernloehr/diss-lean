import NLS.ZakharovShabat.L2SourceGradientUniqueness
import NLS.ZakharovShabat.L2SourceMidpointFourier
import NLS.ZakharovShabat.SourceGradientExponentRestriction

/-! # The physical midpoint gradient independent of contour choices

The actual source derivative restricted to Hilbert directions determines
one continuous physical curve. On a common complex source neighborhood,
every admissible isolating circle constructs that same curve.
-/
noncomputable section
open Set Metric Complex MeasureTheory NLS.LinearVolterra NLS.Fourier
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def sourceMidpointRestrictedCotangent (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (φ : CoeffPair 2) (n : ℤ) : CoeffPair 2 →L[ℂ] ℂ :=
  (fderiv ℂ (fun χ : CoeffPair p => canonicalPeriodicMidpoint hp hp1
    (periodOnePotential χ) (periodOnePotential_mem χ) n) (CoeffPair.exponentInclusion h2p φ)).comp
    (CoeffPair.exponentInclusion h2p)

/-- The selected physical midpoint curve; the theorems below establish its
representation property on a neighborhood of the entire real source locus. -/
def sourceMidpointPhysicalGradientCurve (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (φ : CoeffPair 2) (n : ℤ) : Curve (ℂ × ℂ) :=
  sourcePhysicalGradientCurve (sourceMidpointRestrictedCotangent hp hp1 h2p φ n)

def sourceMidpointPhysicalGradient (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (φ : CoeffPair 2) (n : ℤ) : ℝ → ℂ × ℂ :=
  extend (sourceMidpointPhysicalGradientCurve hp hp1 h2p φ n)

/-- The selected curve represents the actual full Hilbert restriction and
is realized by a constructed contour at every signed index. -/
theorem exists_global_source_midpoint_physical_gradient
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧
      ∀ φ : CoeffPair 2, CoeffPair.exponentInclusion h2p φ ∈ W → ∀ n : ℤ,
        SourcePhysicalGradientRepresents (sourceMidpointRestrictedCotangent hp hp1 h2p φ n)
          (sourceMidpointPhysicalGradientCurve hp hp1 h2p φ n) ∧
        ∃ c : ℂ, ∃ r : ℝ, 0 < r ∧ sourceMidpointPhysicalGradientCurve hp hp1 h2p φ n =
          l2MidpointGradientCurve (sourcePhysicalL2 φ) c r := by
  obtain ⟨W,hW,hreal,hgradient⟩ := exists_global_source_midpoint_l2_gradient hp hp1 h2p
  refine ⟨W,hW,hreal,?_⟩
  intro φ hφ n
  obtain ⟨c,r,hr,hformula⟩ := hgradient φ hφ n
  have hg : SourcePhysicalGradientRepresents (sourceMidpointRestrictedCotangent hp hp1 h2p φ n)
      (l2MidpointGradientCurve (sourcePhysicalL2 φ) c r) := hformula
  have he : sourceMidpointPhysicalGradientCurve hp hp1 h2p φ n =
      l2MidpointGradientCurve (sourcePhysicalL2 φ) c r := sourcePhysicalGradientCurve_eq_of_represents hg
  refine ⟨?_,c,r,hr,he⟩
  rw [he]
  exact hg

/-- Every geometrically admissible circle gives the same physical curve,
including its endpoints and even when the enclosed periodic gap is collapsed. -/
theorem exists_global_source_midpoint_contour_independent
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧
      ∀ φ : CoeffPair 2, CoeffPair.exponentInclusion h2p φ ∈ W →
      ∀ (n : ℤ) (c : ℂ) (r : ℝ), 0 < r →
      let ψ := CoeffPair.exponentInclusion h2p φ
      canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ∈ ball c r →
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ∈ ball c r →
      closedBall c r ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n →
        sourceMidpointPhysicalGradientCurve hp hp1 h2p φ n = l2MidpointGradientCurve (sourcePhysicalL2 φ) c r := by
  obtain ⟨W,hW,hreal,hformula⟩ := exists_global_source_midpoint_l2_gradient_contour hp hp1 h2p
  refine ⟨W,hW,hreal,?_⟩
  intro φ hφ n c r hr
  dsimp only
  intro ha hb hi
  exact sourcePhysicalGradientCurve_eq_of_represents (L := sourceMidpointRestrictedCotangent hp hp1 h2p φ n)
    (g := l2MidpointGradientCurve (sourcePhysicalL2 φ) c r) (hformula φ hφ n c r hr ha hb hi)

/-- At real Hilbert sources, exponent inclusion restricts to the same actual cotangent. -/
theorem sourceMidpointRestrictedCotangent_eq_hilbert_of_real
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (φ : CoeffPair 2) (hφ : φ ∈ realTypeSourceLocus 2) (n : ℤ) :
    sourceMidpointRestrictedCotangent hp hp1 h2p φ n =
      fderiv ℂ (fun χ : CoeffPair 2 => canonicalPeriodicMidpoint (by simp) (by norm_num)
        (periodOnePotential χ) (periodOnePotential_mem χ) n) φ :=
  (fderiv_canonicalPeriodicMidpoint_source_exponent (by simp) hp (by norm_num) hp1 h2p ⟨φ,hφ⟩ n).symm

/-- The physical midpoint curve at a real source is independent of the finite
ambient exponent, as well as of its constructing contour. -/
theorem sourceMidpointPhysicalGradientCurve_exponent_of_real
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (φ : CoeffPair 2) (hφ : φ ∈ realTypeSourceLocus 2) (n : ℤ) :
    sourceMidpointPhysicalGradientCurve hp hp1 h2p φ n =
      sourceMidpointPhysicalGradientCurve (by simp) (by norm_num) (le_rfl : (2 : ℝ≥0∞) ≤ 2) φ n := by
  unfold sourceMidpointPhysicalGradientCurve
  rw [sourceMidpointRestrictedCotangent_eq_hilbert_of_real hp hp1 h2p φ hφ,
    sourceMidpointRestrictedCotangent_eq_hilbert_of_real (by simp) (by norm_num) le_rfl φ hφ]

variable {q : ℝ≥0∞} [Fact (1 ≤ q)] [q.HolderConjugate p]

/-- The existing G.7 vector realizes the unique midpoint gradient, without
any contour parameters in the resulting coefficient identity. -/
theorem exists_global_sourceG7_canonical_midpoint_realization
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧
      ∀ φ : CoeffPair 2, CoeffPair.exponentInclusion h2p φ ∈ W → ∀ n : ℤ,
        SourcePhysicalGradientRepresents (sourceMidpointRestrictedCotangent hp hp1 h2p φ n)
          (sourceMidpointPhysicalGradientCurve hp hp1 h2p φ n) ∧
        L2RootGradientFourierRealizes (sourceMidpointPhysicalGradient hp hp1 h2p φ n)
          (sourceG7MidpointGradient (q := q) hp hp1 (CoeffPair.exponentInclusion h2p φ) n) := by
  obtain ⟨W,hW,hreal,hgradient⟩ := exists_global_source_midpoint_physical_gradient hp hp1 h2p
  refine ⟨W,hW,hreal,?_⟩
  have hcoeff (f : ℝ → ℂ) (k : ℤ) : intervalFourierCoefficient 1 f k = unitFourierCoefficient f k := by
    rw [intervalFourierCoefficient_eq_fourierCoeffOn (by norm_num),unitFourierCoefficient_eq_fourierCoeffOn]
  intro φ hφ n
  have hint := (hgradient φ hφ n).1
  refine ⟨hint,fun k => ?_⟩
  rw [(sourceG7MidpointGradient_coefficients (q := q) hp hp1 _ n k).1,
    (sourceG7MidpointGradient_coefficients (q := q) hp hp1 _ n k).2]
  constructor
  · have hdir : CoeffPair.inlCLM (lp.single p k (1 : ℂ)) =
        CoeffPair.exponentInclusion h2p (CoeffPair.ofFinsupp (p := 2) (Finsupp.single k 1,0)) := by
      rw [CoeffPair.exponentInclusion_ofFinsupp]
      apply (CoeffPair.toMax p).injective
      apply Prod.ext <;> ext m <;> simp [lp.single_apply,Pi.single_apply,Finsupp.single_apply,eq_comm]
    rw [hdir]
    change sourceMidpointRestrictedCotangent hp hp1 h2p φ n _ = _
    rw [hint,source_physical_gradient_pairing_single_fst,hcoeff]
    rfl
  · have hdir : CoeffPair.inrCLM (lp.single p (-k) (1 : ℂ)) =
        CoeffPair.exponentInclusion h2p (CoeffPair.ofFinsupp (p := 2) (0,Finsupp.single (-k) 1)) := by
      rw [CoeffPair.exponentInclusion_ofFinsupp]
      apply (CoeffPair.toMax p).injective
      apply Prod.ext <;> ext m <;> simp [lp.single_apply,Pi.single_apply,Finsupp.single_apply,eq_comm]
    rw [hdir]
    change sourceMidpointRestrictedCotangent hp hp1 h2p φ n _ = _
    rw [hint,source_physical_gradient_pairing_single_snd,neg_neg,hcoeff]
    rfl

/-- G.7 midpoint summability for the unique physical gradient, with the
original H1 source and finite conjugate coefficient norm. -/
theorem exists_global_sourceG7_canonical_midpoint_memlp
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧
      ∀ a : ScalarDomain 2 × ScalarDomain 2,
        CoeffPair.exponentInclusion h2p (sobolevSourceInclusion a) ∈ W →
        Memℓp (fun n : ℤ => sourceG7MidpointGradient (q := q) hp hp1
          (CoeffPair.exponentInclusion h2p (sobolevSourceInclusion a)) n) p ∧ ∀ n : ℤ,
          L2RootGradientFourierRealizes (sourceMidpointPhysicalGradient hp hp1 h2p (sobolevSourceInclusion a) n)
            (sourceG7MidpointGradient (q := q) hp hp1 (CoeffPair.exponentInclusion h2p (sobolevSourceInclusion a)) n) := by
  obtain ⟨U,hU,hUr,hu⟩ := exists_global_sourceG7_canonical_midpoint_realization (q := q) hp hp1 h2p
  obtain ⟨V,hV,hVr,hv⟩ := sourceLemmaG7_corrected (q := q) hp hp1 h2p
  refine ⟨U ∩ V,hU.inter hV,fun φ hφ => ⟨hUr hφ,hVr hφ⟩,?_⟩
  intro a ha
  exact ⟨(hv a ha.2).1,fun n => (hu _ ha.1 n).2⟩

end NLS.ZakharovShabat
