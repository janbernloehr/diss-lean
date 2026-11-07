import NLS.Articles.MKdVNLSHierarchies.PhysicalMiuraEigenfunction
import NLS.Fourier.WeakIntervalH2

/-! # Lemma 2 on the entire weak interval H2 input domain

The source is an arbitrary pair of actual L2 classes with two L2 weak
derivatives. Its weak first-order eigen-equation is transferred to the
constructed AC representative before applying the physical Miura identity.
No periodicity or boundary condition is imposed on either eigenfunction.
-/
noncomputable section
open Set Complex MeasureTheory NLS.Fourier NLS.ZakharovShabat NLS.MKdV
namespace NLS.Articles.MKdVNLSHierarchies

theorem lemma2_weak_intervalH2 (a : ScalarDomain 2) (z : ℂ) (f : WeakIntervalH2 × WeakIntervalH2)
    (he : ∀ᵐ x ∂volume.restrict (Ioc (0:ℝ) 1),
      (I*f.1.first x+periodOneSobolevSynthesis a (x : AddCircle (2:ℝ))*f.2.value x,
       -I*f.2.first x+periodOneSobolevSynthesis a (x : AddCircle (2:ℝ))*f.1.value x) =
         z • (f.1.value x,f.2.value x)) :
    ∃ F₁ F₂ : ℝ → ℂ, Continuous F₁ ∧ Continuous F₂ ∧
      AbsolutelyContinuousOnInterval F₁ 0 1 ∧ AbsolutelyContinuousOnInterval F₂ 0 1 ∧
      f.1.value =ᵐ[volume.restrict (Ioc (0:ℝ) 1)] F₁ ∧
      f.2.value =ᵐ[volume.restrict (Ioc (0:ℝ) 1)] F₂ ∧
      ∀ᵐ x ∂volume.restrict (Ioc (0:ℝ) 1),
        -deriv (deriv (fun y => F₁ y+I*F₂ y)) x+
          miuraPotential (fun y => periodOneSobolevSynthesis a (y : AddCircle (2:ℝ))) x*(F₁ x+I*F₂ x) =
            z^2*(F₁ x+I*F₂ x) := by
  obtain ⟨F₁,hF₁c,hF₁a,hf₁,hF₁d⟩ := f.1.exists_ac_representative
  obtain ⟨F₂,hF₂c,hF₂a,hf₂,hF₂d⟩ := f.2.exists_ac_representative
  have hphysical : ∀ᵐ x ∂volume.restrict (Ioc (0:ℝ) 1),
      physicalOperator (fun y => (periodOneSobolevSynthesis a (y : AddCircle (2:ℝ)),
        periodOneSobolevSynthesis a (y : AddCircle (2:ℝ)))) (fun y => (F₁ y,F₂ y)) x =
          z • (F₁ x,F₂ x) := by
    filter_upwards [he,hf₁,hf₂,hF₁d,hF₂d] with x hxe hx₁ hx₂ hxd₁ hxd₂
    change (I*deriv F₁ x+periodOneSobolevSynthesis a (x : AddCircle (2:ℝ))*F₂ x,
      -I*deriv F₂ x+periodOneSobolevSynthesis a (x : AddCircle (2:ℝ))*F₁ x) = z • (F₁ x,F₂ x)
    rw [hxd₁.deriv,hxd₂.deriv,← hx₁,← hx₂]
    exact hxe
  have hglobal : ∀ᵐ x : ℝ, x ∈ Icc (0:ℝ) 1 →
      physicalOperator (fun y => (periodOneSobolevSynthesis a (y : AddCircle (2:ℝ)),
        periodOneSobolevSynthesis a (y : AddCircle (2:ℝ)))) (fun y => (F₁ y,F₂ y)) x =
          z • (F₁ x,F₂ x) := by
    rw [restrict_Ioc_eq_restrict_Icc] at hphysical
    exact (ae_restrict_iff' measurableSet_Icc).mp hphysical
  refine ⟨F₁,F₂,hF₁c,hF₂c,hF₁a,hF₂a,hf₁,hf₂,?_⟩
  have hs := ae_restrict_of_ae (s := Ioc (0:ℝ) 1)
    (lemma2_h1_arbitrary_eigenfunction a z (fun y => (F₁ y,F₂ y)) hF₁a hF₂a hglobal)
  filter_upwards [hs,ae_restrict_mem measurableSet_Ioc,
    ae_restrict_of_ae (show ∀ᵐ x : ℝ, x ≠ (1:ℝ) from by simp [ae_iff,measure_singleton])]
      with x hx hxi hx1
  exact hx ⟨hxi.1,lt_of_le_of_ne hxi.2 hx1⟩

end NLS.Articles.MKdVNLSHierarchies
