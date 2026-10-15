import NLS.ZakharovShabat.SourceSection20Original
import NLS.ZakharovShabat.SourceSobolevMomentumNormalization

/-! # The original Section 20 family and physical momentum

The retained Section 19 primitive gives the physical H₂ contour. The
original angle cotangent has momentum bracket 2πn on every real H¹
source with the selected gap open. Complex germs retain this same family;
each index also has an open H¹ domain containing all its real open-gap
sources. No intersection over infinitely many indices is taken.
-/
noncomputable section
open Set Metric Filter Topology Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
namespace SourceSection20Data
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
  {W₀ W V Wa B U : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
  {D : SourceSection17OriginalData hp hp1 W₀ W V s}
  {A : SourceAbelianMomentAtlas hp hp1 Wa s} (Q : SourceSection20Data D A B U)
include Q

/-- The physical H₂ contour uses exactly the primitive retained in Section 19. -/
theorem momentum_contour (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    ∃ T : ℝ, 0 < T ∧ ∀ R : ℝ, T ≤ R →
      sourceFiniteGapNLSHamiltonian hp hp1 φ hf 2 =
        (-I/Real.pi : ℂ)*(∮ z in C(0,R), (sourceFullAbelianPrimitive hp hp1 B 0 (z,φ.val))^2) := by
  obtain ⟨C⟩ := Q.charts φ.val (Q.real_subset φ.property)
  exact exists_sourceFullAbelian_momentum_contour_of_chart φ hf C

/-- The actual contour bracket has the exact integer normalization at every
finite source exponent at least two, with the original psi roots. -/
theorem momentum_contour_bracket (h2p : (2 : ℝ≥0∞) ≤ p)
    (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    ∃ T : ℝ, 0 < T ∧ ∀ R : ℝ, T ≤ R →
      sphere (0 : ℂ) R ⊆ sourceCanonicalRootDomain hp hp1 φ.val →
      ∀ n : ℤ, canonicalPeriodicGap hp hp1 (periodOnePotential φ.val)
        (periodOnePotential_mem φ.val) n ≠ 0 →
      sourceAngularThetaFunctionalBracket hp hp1 h2p n s
        (sourceFullAbelianMomentumContour hp hp1 B 0 R) φ.val = 2*(Real.pi : ℂ)*n :=
  D.previous.original_theta_common_domain.exists_finiteGap_momentumContour_bracket
    Q.toSourceFullAbelianDifferentialData A h2p φ hf
end SourceSection20Data

namespace SourceSection20Data
variable {W₀ W V Wa B U : Set (CoeffPair 2)}
  {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
  {D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s}
  {A : SourceAbelianMomentAtlas (by simp) (by norm_num) Wa s}
  (Q : SourceSection20Data D A B U)
include Q

/-- The physical momentum bracket is 2πn at every original real finite-gap source. -/
theorem finiteGap_momentum_bracket
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (n : ℤ) (hn : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential φ.val) (periodOnePotential_mem _) n ≠ 0) :
    sourceSobolevThetaMomentumBracket n s (sourceFiniteGapSobolevPair (by simp) (by norm_num) φ hf) =
      2*(Real.pi : ℂ)*n :=
  D.complex.finiteGap_momentum_bracket_normalized D.previous.original_theta_common_domain
    Q.toSourceFullAbelianDifferentialData A φ hf n hn

/-- H¹ density extends the actual physical bracket, retaining the original angle family. -/
theorem sobolev_momentum_bracket (a : realTypeSobolevSourceLocus) (n : ℤ)
    (hn : canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential (sobolevSourceInclusion a.val))
      (periodOnePotential_mem _) n ≠ 0) :
    sourceSobolevThetaMomentumBracket n s a.val = 2*(Real.pi : ℂ)*n :=
  D.complex.realSobolev_momentum_bracket_normalized D.previous.original_theta_common_domain
    Q.toSourceFullAbelianDifferentialData A a n hn

/-- The original physical bracket has its constant complex germ at every real open-gap H¹ source. -/
theorem sobolev_momentum_bracket_complex_germ (a : realTypeSobolevSourceLocus) (n : ℤ)
    (hn : canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential (sobolevSourceInclusion a.val))
      (periodOnePotential_mem _) n ≠ 0) :
    sourceSobolevThetaMomentumBracket n s =ᶠ[𝓝 a.val] (fun _ => 2*(Real.pi : ℂ)*n) :=
  D.complex.eventually_sobolev_momentum_bracket_normalized D.previous.original_theta_common_domain
    Q.toSourceFullAbelianDifferentialData A a n hn

/-- One open complex H¹ domain for each selected index contains all of its real
open-gap sources and stays inside the original Section 20 domain. -/
theorem exists_sobolev_momentum_domain (n : ℤ) :
    ∃ T : Set (ScalarDomain 2 × ScalarDomain 2), IsOpen T ∧
      (∀ a : realTypeSobolevSourceLocus, canonicalPeriodicGap (by simp) (by norm_num)
        (periodOnePotential (sobolevSourceInclusion a.val)) (periodOnePotential_mem _) n ≠ 0 → a.val ∈ T) ∧
      T ⊆ {a | sobolevSourceInclusion a ∈ U ∧ canonicalPeriodicGap (by simp) (by norm_num)
        (periodOnePotential (sobolevSourceInclusion a)) (periodOnePotential_mem _) n ≠ 0} ∧
      ∀ a ∈ T, sourceSobolevThetaMomentumBracket n s a = 2*(Real.pi : ℂ)*n := by
  let G := {a : ScalarDomain 2 × ScalarDomain 2 | sobolevSourceInclusion a ∈ U ∧
    canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential (sobolevSourceInclusion a))
      (periodOnePotential_mem _) n ≠ 0 ∧ sourceSobolevThetaMomentumBracket n s a = 2*(Real.pi : ℂ)*n}
  refine ⟨interior G,isOpen_interior,?_,?_,?_⟩
  · intro a hn
    have hL := continuousAt_canonicalPeriodicLeft_periodOne_of_realType
      (by simp) (by norm_num) (sobolevSourceInclusion a.val) a.property n
    have hR := continuousAt_canonicalPeriodicRight_periodOne_of_realType
      (by simp) (by norm_num) (sobolevSourceInclusion a.val) a.property n
    have hgap := ((hR.sub hL).comp sobolevSourceInclusion.continuous.continuousAt).eventually
      (isOpen_compl_singleton.mem_nhds hn)
    have hU : ∀ᶠ b in 𝓝 a.val, sobolevSourceInclusion b ∈ U :=
      sobolevSourceInclusion.continuous.continuousAt.preimage_mem_nhds
      (Q.source_open.mem_nhds (Q.real_subset a.property))
    apply mem_interior_iff_mem_nhds.mpr
    exact hU.and (hgap.and (Q.sobolev_momentum_bracket_complex_germ a n hn))
  · intro a ha
    exact ⟨(interior_subset ha).1,(interior_subset ha).2.1⟩
  · intro a ha
    exact (interior_subset ha).2.2
end SourceSection20Data

/-- The original constructor supplies every package used by the physical
H¹ momentum identity, simultaneously for every real source and index. -/
theorem sourceSection20_original_momentum :
    ∃ W₀ W V : Set (CoeffPair 2), ∃ s,
    ∃ D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s,
    ∃ Wa : Set (CoeffPair 2), ∃ A : SourceAbelianMomentAtlas (by simp) (by norm_num) Wa s,
    ∃ B U : Set (CoeffPair 2), ∃ _Q : SourceSection20Data D A B U,
      ∀ a : realTypeSobolevSourceLocus, ∀ n : ℤ, canonicalPeriodicGap (by simp) (by norm_num)
        (periodOnePotential (sobolevSourceInclusion a.val)) (periodOnePotential_mem _) n ≠ 0 →
        sourceSobolevThetaMomentumBracket n s a.val = 2*(Real.pi : ℂ)*n := by
  obtain ⟨W₀,W,V,s,D,Wa,A,B,U,Q⟩ := sourceSection20_original (p := 2) (by simp) (by norm_num)
  exact ⟨W₀,W,V,s,D,Wa,A,B,U,Q,Q.sobolev_momentum_bracket⟩

end NLS.ZakharovShabat
