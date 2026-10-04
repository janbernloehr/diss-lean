import NLS.SequenceSpaces.ComplexSignInvariance
import NLS.SequenceSpaces.FiniteCenterBall
import NLS.ZakharovShabat.SourceFrequencyBirkhoffChart

/-! # Complex sign symmetries of the actual frequency

Real action invariance, real-compatible inverse charts, and holomorphic
uniqueness extend every center-fixing coordinate sign symmetry to a
complex ball. The result holds in the full target sequence norm and
allows infinite sign selections. Analytic descent remains separate.
-/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W₀ B X U : Set (CoeffPair p)} {t : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
  {D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t} {φ : realTypeSourceSubmodule p}
namespace SourceBirkhoffInverseChart

/-- Transport source action invariance to the rectangular real form. -/
theorem lifted_real_action_invariance {F : Type*}
    (C : SourceBirkhoffInverseChart D φ U) (f : CoeffPair p → F)
    (hinv : ∀ a b : realTypeSourceSubmodule p, b ∈ sourceRealActionLevelSet hp hp1 a →
      f b.val = f a.val)
    (z w : Coeff p × Coeff p) (hz : z ∈ C.target) (hw : w ∈ C.target)
    (hzr : z ∈ Coeff.realPairLocus p) (hwr : w ∈ Coeff.realPairLocus p)
    (he : ∀ n, w.1 n^2+w.2 n^2 = z.1 n^2+z.2 n^2) :
    f (C.inverse w) = f (C.inverse z) := by
  obtain ⟨a,rfl⟩ := (Coeff.mem_realPairLocus_iff z).mp hzr
  obtain ⟨b,rfl⟩ := (Coeff.mem_realPairLocus_iff w).mp hwr
  apply hinv (C.realInverse a hz) (C.realInverse b hw)
  apply C.realInverse_mem_actionLevelSet a b hz hw
  intro n
  have h := he n
  change (b.1 n:ℂ)^2+(b.2 n:ℂ)^2 = (a.1 n:ℂ)^2+(a.2 n:ℂ)^2 at h
  have hr : b.1 n^2+b.2 n^2 = a.1 n^2+a.2 n^2 := by exact_mod_cast h
  unfold RealCoeff.pairAction
  rw [hr]

/-- Any analytic action invariant source map has complex sign symmetry
on a real-centered ball contained in its inverse chart. -/
theorem complex_sign_invariance {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (C : SourceBirkhoffInverseChart D φ U) (f : CoeffPair p → F)
    (hf : AnalyticOnNhd ℂ (f ∘ C.inverse) C.target)
    (hinv : ∀ a b : realTypeSourceSubmodule p, b ∈ sourceRealActionLevelSet hp hp1 a →
      f b.val = f a.val)
    (c : Coeff p × Coeff p) (hc : c ∈ Coeff.realPairLocus p)
    (R : ℝ) (hR : 0 < R) (hball : ball c R ⊆ C.target)
    (e d : ℤ → Bool) (hfix : Coeff.pairSignChange e d c = c)
    (z : Coeff p × Coeff p) (hz : z ∈ ball c R) :
    f (C.inverse (Coeff.pairSignChange e d z)) = f (C.inverse z) := by
  exact Coeff.eqOn_pairSignChange_of_real_action_invariance (f ∘ C.inverse) c R hR hc
    (hf.mono hball) (fun z hz w hw hzr hwr he =>
      C.lifted_real_action_invariance f hinv z w (hball hz) (hball hw) hzr hwr he) e d hfix hz

end SourceBirkhoffInverseChart

/-- Construct a common complex ball centered at a finite truncation and
containing the original Birkhoff point. Both actual sequences are analytic
and invariant under every independent sign selection outside that finite
block. The chart, finite block, and radius precede all target exponents. -/
theorem exists_sourceFrequency_complexTailSignInvariant (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
    ∃ A : SourceAbelianMomentAtlas hp hp1 W s,
    ∃ W₀ B X : Set (CoeffPair p), ∃ t : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
    ∃ D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t,
    ∃ U : Set (CoeffPair p), IsOpen U ∧ realTypeSourceLocus p ⊆ U ∧
      ∀ φ : realTypeSourceSubmodule p, ∃ C : SourceBirkhoffInverseChart D φ U,
        ∃ S : Finset ℤ, ∃ R : ℝ,
        let c := Coeff.truncatePair S (sourceBirkhoffMap hp hp1 t φ.val)
        0 < R ∧ sourceBirkhoffMap hp hp1 t φ.val ∈ ball c R ∧ ball c R ⊆ C.target ∧
        (∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], r ≠ ⊤ → 1 < r → ENNReal.ofReal (p.toReal/2) ≤ r →
          AnalyticOnNhd ℂ (A.frequencySequence r ∘ C.inverse) (ball c R) ∧
          (∀ z ∈ ball c R, ∀ n,
            A.frequencySequence r (C.inverse z) n = A.renormalizedFrequency n (C.inverse z)) ∧
          ∀ e d : ℤ → Bool, (∀ n ∈ S, e n = false) → (∀ n ∈ S, d n = false) →
            ∀ z ∈ ball c R,
              A.frequencySequence r (C.inverse (Coeff.pairSignChange e d z)) =
                A.frequencySequence r (C.inverse z)) ∧
        (∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], r ≠ ⊤ → 1 < r → ENNReal.ofReal (p.toReal/3) ≤ r →
          AnalyticOnNhd ℂ (A.actionFrequencyCorrectionSequence r ∘ C.inverse) (ball c R) ∧
          (∀ z ∈ ball c R, ∀ n,
            A.actionFrequencyCorrectionSequence r (C.inverse z) n =
              A.renormalizedFrequency n (C.inverse z)+z.1 n^2+z.2 n^2) ∧
          ∀ e d : ℤ → Bool, (∀ n ∈ S, e n = false) → (∀ n ∈ S, d n = false) →
            ∀ z ∈ ball c R,
              A.actionFrequencyCorrectionSequence r (C.inverse (Coeff.pairSignChange e d z)) =
                A.actionFrequencyCorrectionSequence r (C.inverse z)) := by
  obtain ⟨W,P,s,A,hs,W₀,B,X,t,D,U,hU,hreal,_,hcharts⟩ := exists_sourceFrequency_birkhoffCharts hp hp1
  refine ⟨W,s,A,W₀,B,X,t,D,U,hU,hreal,?_⟩
  intro φ
  obtain ⟨C,hfreq,hcorr,_⟩ := hcharts φ
  obtain ⟨S,R,hR,hbase,hball⟩ := Coeff.exists_finiteCenter_ball hp C.target C.target_open _ C.center_mem
  have hc : Coeff.truncatePair S (sourceBirkhoffMap hp hp1 t φ.val) ∈ Coeff.realPairLocus p :=
    Coeff.truncatePair_mem_realPairLocus S _ ((Coeff.mem_realPairLocus_iff _).mpr
      ⟨sourceRealBirkhoffMap hp hp1 t φ,D.real_map_complex_inclusion φ⟩)
  refine ⟨C,S,R,hR,hbase,hball,?_,?_⟩
  · intro r inst hr hr1 hpr
    obtain ⟨ha,he⟩ := hfreq r hr hr1 hpr
    refine ⟨ha.mono hball,fun z hz => he z (hball hz),?_⟩
    intro e d he hd z hz
    exact C.complex_sign_invariance _ ha
      (fun a b hab => A.frequencySequence_real_eq_of_actions A hs hs a b hab r)
      _ hc R hR hball e d (Coeff.pairSignChange_truncatePair S _ e d he hd) z hz
  · intro r inst hr hr1 hpr
    obtain ⟨ha,he⟩ := hcorr r hr hr1 hpr
    refine ⟨ha.mono hball,fun z hz => he z (hball hz),?_⟩
    intro e d he hd z hz
    exact C.complex_sign_invariance _ ha
      (fun a b hab => A.actionFrequencyCorrectionSequence_real_eq_of_actions A hs hs a b hab r)
      _ hc R hR hball e d (Coeff.pairSignChange_truncatePair S _ e d he hd) z hz

end NLS.ZakharovShabat
