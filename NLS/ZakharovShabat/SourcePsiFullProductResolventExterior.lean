import NLS.ZakharovShabat.SourcePsiFullProductVariation
import NLS.ZakharovShabat.SourcePsiRootResolventExterior

/-!
# Root-resolvent formula for the full product variation

Restoring the zero-index factor adds its root motion back to the
deleted numerator derivative. The resulting full variation is the
full root product times the complete actual-root resolvent, with no
deleted-coordinate assumption. Exterior resolvent decay then applies
to every root direction.
-/

noncomputable section
open Set Filter Topology Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Away from the roots, an absolutely summable actual-root resolvent
gives the exact full product variation. -/
theorem sourcePsiFullProductVariation_eq_product_mul_resolvent
    (hp : p ≠ ⊤) (hp1 : 1 < p) (a h : Coeff p) (z : ℂ)
    (havoid : ∀ m : ℤ, z ≠ displacedRoots a m)
    (hsum : Summable (fun m : ℤ => h m / (displacedRoots a m-z))) :
    sourcePsiFullProductVariation a h z = jointSingleSpectralProduct (z,a) *
      ∑' m : ℤ, h m / (displacedRoots a m-z) := by
  let F : ℤ → ℂ := fun m => h m / (displacedRoots a m-z)
  have hcut (N : ℕ) :
      (∑ m ∈ (Finset.Icc (-(N:ℤ)) (N:ℤ)).erase 0, F m) =
        (∑ m ∈ Finset.Icc (-(N:ℤ)) (N:ℤ), F m)-F 0 := by
    have hn : (0:ℤ) ∈ Finset.Icc (-(N:ℤ)) (N:ℤ) := by simp
    exact eq_sub_of_add_eq (Finset.sum_erase_add _ F hn)
  have hlimit : Tendsto
      (fun N : ℕ => ∑ m ∈ (Finset.Icc (-(N:ℤ)) (N:ℤ)).erase 0, F m)
      atTop (𝓝 ((∑' m : ℤ, F m)-F 0)) := by
    simpa only [Function.comp_def, hcut] using
      (hsum.hasSum.comp Finset.tendsto_Icc_neg).sub_const (F 0)
  have hpsi := sourcePsiCandidateVariation_eq_mul_resolventLimit
    hp hp1 0 a h z ((∑' m : ℤ, F m)-F 0) (fun m _ => havoid m) hlimit
  have hproduct : jointSingleSpectralProduct (z,a) =
      (z-displacedRoots a 0)*sourcePsiCandidate 0 (z,a) := by
    rw [jointSingleSpectralProduct_eq_deleted hp hp1 0]
    unfold sourcePsiCandidate
    ring
  rw [sourcePsiFullProductVariation_eq_deleted_variation hp hp1 0, hpsi, hproduct]
  change -(h 0*sourcePsiCandidate 0 (z,a)) +
    (z-displacedRoots a 0)*(sourcePsiCandidate 0 (z,a)*
      ((∑' m : ℤ, F m)-h 0/(displacedRoots a 0-z))) =
    ((z-displacedRoots a 0)*sourcePsiCandidate 0 (z,a))*(∑' m : ℤ, F m)
  have hden : displacedRoots a 0-z ≠ 0 := sub_ne_zero.mpr (havoid 0).symm
  field_simp [hden]
  ring

/-- On the separated exterior, the full variation has its complete
resolvent formula and the resolvent is uniformly arbitrarily small. -/
theorem exists_threshold_sourcePsiFullProductVariation_resolvent_small
    (hp : p ≠ ⊤) (hp1 : 1 < p) (a h : Coeff p)
    {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi/4)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ →
      (∀ m : ℤ, r ≤ ‖z-(Real.pi:ℂ)*m‖) →
      sourcePsiFullProductVariation a h z = jointSingleSpectralProduct (z,a)*
        ∑' m : ℤ, h m/(displacedRoots a m-z) ∧
      ‖∑' m : ℤ, h m/(displacedRoots a m-z)‖ ≤ ε := by
  obtain ⟨Rsum,hRsum⟩ := exists_threshold_actualRootResolvent_sum_small hp a h hr hrπ hε
  obtain ⟨Ravoid,hRavoid⟩ := exists_threshold_actualRoots_avoided hp a hr
  refine ⟨max Rsum Ravoid,?_⟩
  intro z hz hsep
  have hsum := hRsum z ((le_max_left _ _).trans hz) hsep
  have havoid := hRavoid z ((le_max_right _ _).trans hz) hsep
  exact ⟨sourcePsiFullProductVariation_eq_product_mul_resolvent hp hp1 a h z
    havoid hsum.1.of_norm, (norm_tsum_le_tsum_norm hsum.1).trans hsum.2⟩

end NLS.ZakharovShabat
