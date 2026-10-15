import NLS.ZakharovShabat.SourceSecondMomentMixed
import NLS.ZakharovShabat.SourceSection19Original
import NLS.ZakharovShabat.SourceFrequencySequenceAnalytic
import NLS.ZakharovShabat.SourceSecondMomentFrequencyTheorem20_4

/-!
# One original source domain for Section 20

The original normalized root family supplies the actual contour moments.
Their estimates, convergent frequency sum, and analytic sequence maps share
one connected source neighborhood with all of Section 19. The entire real
locus is retained, and all auxiliary target exponents use the same domain.
-/
noncomputable section
open Set Metric Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
  {W₀ W V : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

structure SourceSection20Data (D : SourceSection17OriginalData hp hp1 W₀ W V s)
    {Wa : Set (CoeffPair p)} (A : SourceAbelianMomentAtlas hp hp1 Wa s)
    (B U : Set (CoeffPair p)) : Prop extends SourceSection19Data hp hp1 B U where
  roots : SourcePsiSquaredGapComplexExtension hp hp1 W s
  original_subset : U ⊆ V
  moment_subset : U ⊆ A.domain
  moment_estimates : ∀ φ ∈ U, ∃ T : Set (CoeffPair p), IsOpen T ∧ φ ∈ T ∧ T ⊆ U ∧
    SourceSecondMomentMixedData A T
  summable : ∀ ψ ∈ U, ∀ n, Summable (fun k => ‖A.moment n k 2 ψ‖)
  frequency_analytic : ∀ n, AnalyticOnNhd ℂ (A.renormalizedFrequency n) U
  frequency_uniform : ∀ φ ∈ U, ∃ T : Set (CoeffPair p), IsOpen T ∧ φ ∈ T ∧ T ⊆ U ∧ ∀ n : ℤ,
    TendstoUniformlyOn
      (fun (N : ℕ) ψ => -(4/(2*Real.pi):ℂ)*∑ k ∈ Finset.Icc (-(N : ℤ)) N, A.moment n k 2 ψ)
      (A.renormalizedFrequency n) atTop T
  sequence : ∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], r ≠ ⊤ → 1 < r → ENNReal.ofReal (p.toReal/2) ≤ r →
    (∀ ψ ∈ U, ∀ n, A.frequencySequence r ψ n = A.renormalizedFrequency n ψ) ∧
      AnalyticOnNhd ℂ (A.frequencySequence r) U
  frequency_mixed : ∀ φ ∈ U, ∃ T : Set (CoeffPair p), IsOpen T ∧ φ ∈ T ∧ T ⊆ U ∧
    ∃ g : CoeffPair p → Coeff (ENNReal.ofReal (p.toReal/3)), ∃ h : CoeffPair p → CoeffOnePlus,
      (∀ ψ ∈ T, ∀ n, A.renormalizedFrequency n ψ+(sourcePeriodicGapDisplacement hp hp1 ψ n)^2/2 =
        g ψ n+(h ψ).1 n) ∧
      (∃ M : ℝ, 0 ≤ M ∧ ∀ ψ ∈ T, ‖g ψ‖ ≤ M) ∧
      ∀ (r : ℝ≥0∞) (hr1 : 1 < r) (hr : r ≠ ⊤),
        ∃ M : ℝ, 0 ≤ M ∧ ∀ ψ ∈ T, ‖CoeffOnePlus.toCoeff r hr1 hr (h ψ)‖ ≤ M

/-- Construct Section 20 with the already chosen original roots, retaining
one Section 19 primitive and one domain for every moment and frequency. -/
theorem SourceSection17OriginalData.exists_section20
    (D : SourceSection17OriginalData hp hp1 W₀ W V s) :
    ∃ Wa : Set (CoeffPair p), ∃ A : SourceAbelianMomentAtlas hp hp1 Wa s,
      ∃ B U : Set (CoeffPair p), SourceSection20Data D A B U := by
  classical
  have hs := D.previous.angular_extension
  have hW : IsOpen W := by
    obtain ⟨E,hE,_⟩ := D.previous.previous.previous.atlas
    exact hE ▸ E.toSourcePsiComplexRootAtlas.isOpen_domain
  have hrealW : realTypeSourceLocus p ⊆ W := D.complex.real_subset.trans D.complex.source_subset
  obtain ⟨Wa,_,_,hlocal⟩ := hs.toSourcePsiNormalizedComplexExtension.exists_moment_localCharts hW hrealW
  choose L hL using hlocal
  let A : SourceAbelianMomentAtlas hp hp1 Wa s := ⟨L⟩
  obtain ⟨Um,hUm,_,hre_m,hm_sub,hm⟩ := A.exists_lemma20_3_refined hs hW hrealW
  obtain ⟨Uf,hUf,_,hre_f,_,habs,han,huniform⟩ := A.exists_analytic_renormalizedFrequency hs hW hrealW
  obtain ⟨Us,hUs,_,hre_s,_,hseq,hcorr⟩ := A.exists_analytic_frequencySequence hs hW hrealW
  let X := Um ∩ (Uf ∩ (Us ∩ V))
  obtain ⟨B,U,hUX,Q⟩ := exists_sourceSection19Data hp hp1 X
    (hUm.inter (hUf.inter (hUs.inter D.complex.source_open)))
    (fun ψ hψ => ⟨hre_m hψ,hre_f hψ,hre_s hψ,D.complex.real_subset hψ⟩)
  refine ⟨Wa,A,B,U,{
    toSourceSection19Data := Q
    roots := hs
    original_subset := fun ψ hψ => (hUX hψ).2.2.2
    moment_subset := fun ψ hψ => (hm_sub (hUX hψ).1).1
    moment_estimates := ?_
    summable := fun ψ hψ => habs ψ (hUX hψ).2.1
    frequency_analytic := fun n => (han n).mono (fun ψ hψ => (hUX hψ).2.1)
    frequency_uniform := ?_
    sequence := ?_
    frequency_mixed := ?_
  }⟩
  · intro φ hφ
    obtain ⟨ρ,hρ,_,hrows⟩ := hm φ (hUX hφ).1
    refine ⟨ball φ ρ ∩ U,isOpen_ball.inter Q.source_open,⟨mem_ball_self hρ,hφ⟩,inter_subset_right,?_⟩
    apply sourceSecondMomentMixedData_of_refined
    intro r hr hr1 hpr
    obtain ⟨M,hM,hb⟩ := hrows r hr hr1 hpr
    exact ⟨M,hM,fun ψ hψ => hb ψ hψ.1⟩
  · intro φ hφ
    obtain ⟨T,hT,hφT,_,hconv⟩ := huniform φ (hUX hφ).2.1
    exact ⟨T ∩ U,hT.inter Q.source_open,⟨hφT,hφ⟩,inter_subset_right,
      fun n => (hconv n).mono inter_subset_left⟩
  · intro r inst hr hr1 hpr
    obtain ⟨he,ha⟩ := hseq r hr hr1 hpr
    exact ⟨fun ψ hψ => he ψ (hUX hψ).2.2.1,ha.mono (fun ψ hψ => (hUX hψ).2.2.1)⟩
  · intro φ hφ
    obtain ⟨T,hT,hφT,_,hb⟩ := hcorr φ (hUX hφ).2.2.1
    refine ⟨T ∩ U,hT.inter Q.source_open,⟨hφT,hφ⟩,inter_subset_right,?_⟩
    exact Coeff.exists_onePlus_decomposition_of_refined (T ∩ U) A.frequencyCorrection
      ENNReal.ofReal_ne_top (fun r hr hr1 hpr => by
        obtain ⟨M,hM,hb⟩ := hb r hr hr1 hpr
        exact ⟨M,hM,fun ψ hψ => hb ψ hψ.1⟩)

end NLS.ZakharovShabat
