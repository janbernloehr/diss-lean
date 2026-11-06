import NLS.KdV.HillMiuraFourierLebesgueNormalizedSource
import NLS.ZakharovShabat.SourceGapWeightedEtaRealExponent
import NLS.ZakharovShabat.SourceWeightedEtaComplexAnalytic
import NLS.ZakharovShabat.SourceSection14

/-! # Native analytic eta germs with exact physical real-slice recovery

The bounded weighted p-exponent germ retains the supplied original
Hilbert eta family on EVERY real source in its neighborhood, including
all closed indices. No uniform complex cross-exponent identity is needed.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.KdV
variable {p : ℝ≥0∞} [Fact (1≤p)]

theorem exists_hillMiuraFourierLebesgueEta_germ
    {W₀ W : Set (CoeffPair 2)} {s2 : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
    (H : SourceLemma12_12Data (by norm_num) (by norm_num) W₀ W s2)
    (hp : p≠⊤) (h2p : 2≤p) (t : ℝ) (ht : 0≤t)
    (a0 : WeightedCoeff (Weight.sobolev t) p) (u0 : Coeff 2)
    (ha0 : ∀ n : ℤ, a0.val n=u0 n) (hr0 : periodOneL2Conjugation u0=u0) :
    ∃ V : Set (WeightedCoeff (Weight.sobolev t) p), IsOpen V ∧ a0∈V ∧
      ∃ M : ℝ, ∃ F : WeightedCoeff (Weight.sobolev t) p → Coeff p,
        0≤M ∧ AnalyticOnNhd ℂ F V ∧ ∀ a∈V, ‖F a‖≤M ∧
          ∀ (u : Coeff 2), (∀ n : ℤ, a.val n=u n) → periodOneL2Conjugation u=u →
          ∀ n : ℤ, F a n=(Weight.sobolev t n : ℂ)*
            sourceGapWeightedEtaCoordinate (by norm_num) (by norm_num) n s2 1
              (sourcePhase (hillMiuraDiagonal u)) := by
  have hp1 : 1<p := lt_of_lt_of_le (by norm_num : (1 : ℝ≥0∞)<2) h2p
  obtain ⟨A0,B0,C0,sp,Dp⟩ := sourceSection14 hp hp1
  let J := hillMiuraNormalizedFourierLebesgueDirichletSource (p := p) t
  have hrawreal (n : ℤ) : a0.val (-n)=conj (a0.val n) := by
    rw [ha0,ha0]
    exact (periodOneL2Conjugation_fixed_iff u0).mp hr0 n
  let φ0 : realTypeSourceLocus p :=
    ⟨J a0,isRealType_hillMiuraNormalizedFourierLebesgueDirichletSource t a0 hrawreal⟩
  let w := sourceSobolevSpectralWeight t ht
  obtain ⟨A,hA,hφA,M,hM,hEta⟩ := Dp.complex.exists_local_normalizedWeightedEta_analytic w φ0
  let V : Set (WeightedCoeff (Weight.sobolev t) p) := J ⁻¹' A
  let F : WeightedCoeff (Weight.sobolev t) p → Coeff p := fun a =>
    normalizedWeightedEtaSequence hp hp1 sp w 1 (J a)
  refine ⟨V,hA.preimage J.continuous,hφA,M,F,hM,?_,?_⟩
  · intro a ha
    exact ((hEta 1 (Or.inl rfl)).1 (J a) ha).comp (J.analyticAt a)
  · intro a ha
    refine ⟨((hEta 1 (Or.inl rfl)).2 (J a) ha).1,?_⟩
    intro u hraw hr n
    let φ : realTypeSourceSubmodule 2 :=
      ⟨sourcePhase (hillMiuraDiagonal u),isRealType_sourcePhase _
        (isRealType_hillMiuraDiagonal ⟨u,(periodOneL2Conjugation_fixed_iff u).mp hr⟩)⟩
    have he := H.original_theta_common_domain.toSourceAngularEtaLocalCommonDomainData.gapWeightedEta_real_exponent
      Dp.complex.angular W C0 H.original_theta_common_domain.source_open Dp.complex.source_open
      (Subset.refl _) Dp.complex.source_subset h2p n φ
      (H.original_theta_common_domain.real_subset φ.property)
      (Dp.complex.real_subset (realTypeSourceExponentInclusion h2p φ).property) 1
    have hcoord := ((hEta 1 (Or.inl rfl)).2 (J a) ha).2 n
    have hsource : normalizedWeightedSource w (J a)=CoeffPair.exponentInclusion h2p φ.val :=
      normalizedWeightedSource_hillMiuraFourierLebesgue t ht a h2p u hraw
    change F a n=_
    change normalizedWeightedEtaSequence hp hp1 sp w 1 (J a) n=_
    rw [hcoord,hsource,←he]
    simp only [w,sourceSobolevSpectralWeight_even]
    rfl

end NLS.KdV
