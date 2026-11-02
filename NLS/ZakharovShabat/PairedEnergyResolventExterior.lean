import NLS.ZakharovShabat.SourcePsiRootResolventExterior

/-! # Exterior decay of a paired energy resolvent

An antisymmetric frequency direction pairs into the energy resolvent
remainder. The existing complex l2 root-resolvent estimate gives decay
without losing a power of the frequency.
-/
noncomputable section
open Set Metric Complex Filter Topology
namespace NLS.ZakharovShabat

theorem pairedRootResolvent_eq_energy (rho : ℤ → ℂ) (h : NLS.Coeff 2)
    (c : ℕ+ → ℂ) (sigma z : ℂ)
    (hneg : ∀ k : ℕ+, rho (-(k : ℤ)) = -rho (k : ℤ))
    (hrho : ∀ k : ℕ+, rho (k : ℤ) ≠ 0)
    (hh0 : h 0 = 0) (hhneg : ∀ k : ℕ+, h (-(k : ℤ)) = -h (k : ℤ))
    (hhpos : ∀ k : ℕ+, h (k : ℤ) = -c k*((rho (k : ℤ))^2-sigma)/(2*rho (k : ℤ)))
    (havoid : ∀ j : ℤ, z ≠ rho j)
    (hs : Summable (fun j : ℤ => h j/(rho j-z))) :
    Summable (fun k : ℕ+ => c k*((rho (k : ℤ))^2-sigma)/(z^2-(rho (k : ℤ))^2)) ∧
    (∑' j : ℤ, h j/(rho j-z)) =
      ∑' k : ℕ+, c k*((rho (k : ℤ))^2-sigma)/(z^2-(rho (k : ℤ))^2) := by
  have hi : Function.Injective (fun k : ℕ+ => (k : ℤ)) := by
    intro i j hij
    apply Subtype.ext
    exact Int.ofNat_inj.mp hij
  have hni : Function.Injective (fun k : ℕ+ => -(k : ℤ)) := by
    intro i j hij
    exact hi (neg_injective hij)
  have hp : Summable (fun k : ℕ+ => h (k : ℤ)/(rho (k : ℤ)-z)) := by
    simpa only [Function.comp_def] using! hs.comp_injective hi
  have hn : Summable (fun k : ℕ+ => h (-(k : ℤ))/(rho (-(k : ℤ))-z)) := by
    simpa only [Function.comp_def] using! hs.comp_injective hni
  have he (k : ℕ+) : h (k : ℤ)/(rho (k : ℤ)-z)+h (-(k : ℤ))/(rho (-(k : ℤ))-z) =
      c k*((rho (k : ℤ))^2-sigma)/(z^2-(rho (k : ℤ))^2) := by
    have hm : rho (k : ℤ)-z ≠ 0 := sub_ne_zero.mpr (havoid (k : ℤ)).symm
    have hnz : -rho (k : ℤ)-z ≠ 0 := by
      rw [← hneg k]
      exact sub_ne_zero.mpr (havoid (-(k : ℤ))).symm
    have hden : z^2-(rho (k : ℤ))^2 ≠ 0 := by
      intro he
      rcases (sq_eq_sq_iff_eq_or_eq_neg).mp (sub_eq_zero.mp he) with hz | hz
      · exact havoid (k : ℤ) hz
      · exact havoid (-(k : ℤ)) (hz.trans (hneg k).symm)
    rw [hhneg k,hneg k,hhpos k]
    field_simp [hrho k,hm,hnz,hden]
    ring
  refine ⟨(hp.add hn).congr he,?_⟩
  rw [tsum_int_eq_zero_add_tsum_pnat hs,hh0,zero_div,zero_add,← hp.tsum_add hn]
  exact tsum_congr he

/-- The paired energy remainder is uniformly small on the large separated
exterior, with absolute sums and avoidance of every critical energy. -/
theorem exists_threshold_pairedEnergyResolvent_small
    (rho : ℤ → ℂ) (hlp : Memℓp (fun j => rho j-(Real.pi : ℂ)*j) 2)
    (h : NLS.Coeff 2) (c : ℕ+ → ℂ) (sigma : ℂ)
    (hneg : ∀ k : ℕ+, rho (-(k : ℤ)) = -rho (k : ℤ))
    (hrho : ∀ k : ℕ+, rho (k : ℤ) ≠ 0)
    (hh0 : h 0 = 0) (hhneg : ∀ k : ℕ+, h (-(k : ℤ)) = -h (k : ℤ))
    (hhpos : ∀ k : ℕ+, h (k : ℤ) = -c k*((rho (k : ℤ))^2-sigma)/(2*rho (k : ℤ)))
    {r : ℝ} (hr : 0 < r) (hrpi : r ≤ Real.pi/4) {eps : ℝ} (heps : 0 < eps) :
    ∃ R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → (∀ j : ℤ, r ≤ ‖z-(Real.pi : ℂ)*j‖) →
      (∀ k : ℕ+, z^2 ≠ (rho (k : ℤ))^2) ∧
      Summable (fun k : ℕ+ => c k*((rho (k : ℤ))^2-sigma)/(z^2-(rho (k : ℤ))^2)) ∧
      ‖∑' k : ℕ+, c k*((rho (k : ℤ))^2-sigma)/(z^2-(rho (k : ℤ))^2)‖ ≤ eps := by
  let a : NLS.Coeff 2 := ⟨fun j => rho j-(Real.pi : ℂ)*j,hlp⟩
  have hroots : displacedRoots a = rho := by
    funext j
    dsimp only [displacedRoots,a]
    ring
  obtain ⟨Rs,hs⟩ := exists_threshold_actualRootResolvent_sum_small
    (by norm_num : (2 : ENNReal) ≠ ⊤) a h hr hrpi heps
  obtain ⟨Ra,ha⟩ := exists_threshold_actualRoots_avoided
    (by norm_num : (2 : ENNReal) ≠ ⊤) a hr
  refine ⟨max Rs Ra,?_⟩
  intro z hz hsep
  have hav := ha z ((le_max_right _ _).trans hz) hsep
  rw [hroots] at hav
  have hsum := hs z ((le_max_left _ _).trans hz) hsep
  rw [hroots] at hsum
  have hpair := pairedRootResolvent_eq_energy rho h c sigma z hneg hrho hh0 hhneg hhpos hav hsum.1.of_norm
  refine ⟨?_,hpair.1,?_⟩
  · intro k he
    rcases (sq_eq_sq_iff_eq_or_eq_neg).mp he with he | he
    · exact hav (k : ℤ) he
    · exact hav (-(k : ℤ)) (he.trans (hneg k).symm)
  · rw [← hpair.2]
    exact (norm_tsum_le_tsum_norm hsum.1).trans hsum.2

end NLS.ZakharovShabat
