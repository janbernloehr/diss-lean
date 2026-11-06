import NLS.KdV.HillHminusOneCanonicalRealLabels
import NLS.KdV.HillHminusOneRealGapRoot
import NLS.KdV.HillHminusPhysicalPeriodicLabels
import NLS.KdV.HillHminusOriginalSheets

/-! # Intrinsic labels identify high pairs across different radii

The cutoff in a rough labeling fixes the index of every actual high pair.
It imposes no bound on the L2 norm of a physical source in that neighborhood.
The argument retains multiplicities and applies to collapsed gaps.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
namespace NLS.KdV

/-- An actual pair in any second radius has the endpoints prescribed by
the same intrinsic real labeling. -/
theorem HillHminusRealCharacteristicLabeling.high_pair_of_radius
    {q : PeriodOneHminusOne} {N : ℕ} {r s : ℝ} {lambda : ℕ → ℝ}
    (h : HillHminusRealCharacteristicLabeling q N r lambda)
    (hq : IsRealPeriodOneHminusOne q) (n : ℕ+) (hn : N ≤ (n : ℕ))
    (hp : ∃ l u : ℂ, HillHminusHighGapPair q n s l u) :
    HillHminusHighGapPair q n s (lambda (2*(n : ℕ)-1) : ℂ)
      (lambda (2*(n : ℕ)) : ℂ) := by
  obtain ⟨p,hl,hu⟩ := h.high_pair n hn
  obtain ⟨l,u,hpair⟩ := hp
  obtain ⟨a,b,hab,habpair⟩ := hpair.exists_real_ordered hq
  let t : HillHminusRealHighPair q n s := ⟨a,b,hab,habpair⟩
  have he := p.endpoints_unique t
  rw [hl,hu,he.1,he.2]
  exact t.pair

/-- A common rough labeling identifies the ORIGINAL physical endpoints
without an additional L2 neighborhood or source norm cutoff. -/
theorem HillHminusRealCharacteristicLabeling.physical_high_pair_of_radius
    (p : RealPeriodOneHillPotential) {N : ℕ} {r s : ℝ}
    (h : HillHminusRealCharacteristicLabeling (hillOriginalHminusSource p.val) N r
      (hillHminusRealLabels (hillOriginalHminusSource p.val)
        (hillOriginalHminusSource_real p.val p.property.2)))
    (n : ℕ+) (hn : N ≤ (n : ℕ))
    (hp : ∃ l u : ℂ, HillHminusHighGapPair (hillOriginalHminusSource p.val) n s l u) :
    HillHminusHighGapPair (hillOriginalHminusSource p.val) n s
      (hillRealLabels p.val p.property.1 p.property.2 (2*(n : ℕ)-1))
      (hillRealLabels p.val p.property.1 p.property.2 (2*(n : ℕ))) := by
  have he : hillHminusRealLabels (hillOriginalHminusSource p.val)
      (hillOriginalHminusSource_real p.val p.property.2) =
      hillRealLabels p.val p.property.1 p.property.2 :=
    hillHminusRealLabels_eq_physical p
  simpa only [he] using h.high_pair_of_radius
    (hillOriginalHminusSource_real p.val p.property.2) n hn hp

end NLS.KdV
