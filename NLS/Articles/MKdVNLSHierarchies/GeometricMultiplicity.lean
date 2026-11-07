import NLS.MKdV.MiuraH2Eigenspace
import NLS.Articles.MKdVNLSHierarchies.GapIdentification

/-! # Lemma 3's actual geometric multiplicities

The comparison concerns the entire H2 Hill eigenspace and the original H1
ZS eigenspace. For the positive-index real endpoints both frequencies are
strictly positive, so the exact linear equivalence applies without a generic
gap or simplicity assumption. The ground-slot endpoint identities are in the
existing gap interface; no zero-frequency eigenspace equivalence is asserted.
-/
noncomputable section
open Set Complex NLS.MKdV NLS.KdV NLS.ZakharovShabat
open scoped ComplexConjugate
namespace NLS.Articles.MKdVNLSHierarchies

theorem lemma3_geometric_multiplicity_nonzero (a : ScalarDomain 2) (z : ℂ) (hz : z ≠ 0) :
    Module.finrank ℂ (hillSobolevEigenspace (sobolevMiuraHillPotential a) (z^2)) =
      Module.finrank ℂ
        (periodicEigenspace (by norm_num) (periodOnePotential (sobolevSourceInclusion (a,a))) z) :=
  finrank_miuraH2Eigenspace a z hz

theorem lemma3_independent_eigenfunctions_iff (a : ScalarDomain 2) (z : ℂ) (hz : z ≠ 0) :
    (∃ f : Fin 2 → hillSobolevEigenspace (sobolevMiuraHillPotential a) (z^2), LinearIndependent ℂ f) ↔
      ∃ f : Fin 2 → periodicEigenspace (by norm_num)
        (periodOnePotential (sobolevSourceInclusion (a,a))) z, LinearIndependent ℂ f := by
  let e := miuraH2EigenspaceEquiv a z hz
  constructor
  · rintro ⟨f,hf⟩
    exact ⟨e.symm ∘ f,hf.map' e.symm.toLinearMap (LinearMap.ker_eq_bot.mpr e.symm.injective)⟩
  · rintro ⟨f,hf⟩
    exact ⟨e ∘ f,hf.map' e.toLinearMap (LinearMap.ker_eq_bot.mpr e.injective)⟩

theorem lemma3_geometric_multiplicity_endpoints (a : ScalarDomain 2)
    (ha : ∀ k, a.val k = conj (a.val (-k))) (n : ℕ) (hn : 1 ≤ n) :
    Module.finrank ℂ
      (hillSobolevEigenspace (sobolevMiuraHillPotential a) (miuraHillLabels a ha (2*n-1))) =
      Module.finrank ℂ (periodicEigenspace (by norm_num)
        (periodOnePotential (sobolevSourceInclusion (a,a))) (miuraNLSLeft a n)) ∧
    Module.finrank ℂ
      (hillSobolevEigenspace (sobolevMiuraHillPotential a) (miuraHillLabels a ha (2*n))) =
      Module.finrank ℂ (periodicEigenspace (by norm_num)
        (periodOnePotential (sobolevSourceInclusion (a,a))) (miuraNLSRight a n)) := by
  have hL : miuraNLSLeft a n ≠ 0 := by
    intro he
    have hp := miuraNLSLeft_pos a ha (show (0:ℤ) < n by omega)
    rw [he,zero_re] at hp
    exact lt_irrefl 0 hp
  have hR : miuraNLSRight a n ≠ 0 := by
    intro he
    have hp := (miuraNLSLeft_pos a ha (show (0:ℤ) < n by omega)).trans_le
      (miuraNLSEndpoints_within a n)
    rw [he,zero_re] at hp
    exact lt_irrefl 0 hp
  rw [(lemma3_indexed_endpoints a ha n hn).1,(lemma3_indexed_endpoints a ha n hn).2]
  exact ⟨lemma3_geometric_multiplicity_nonzero a _ hL,lemma3_geometric_multiplicity_nonzero a _ hR⟩

end NLS.Articles.MKdVNLSHierarchies
