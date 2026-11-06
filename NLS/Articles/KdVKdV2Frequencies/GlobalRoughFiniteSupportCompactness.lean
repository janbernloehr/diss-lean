import NLS.Articles.KdVKdV2Frequencies.GlobalRoughGroundEnergyBound
import NLS.KdV.HillMiuraFiniteSupportCompactness

/-! # Actual rough preimages of targets with fixed finite support

A finite signed target has an original physical representative. Its actual
gap tail closes. Uniform ground-energy control and the original Dirac
compact container then give norm compactness in H-minus-one.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.KdV
open scoped ENNReal Classical
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

/-- Finite support of the SAME signed weak target closes the actual rough
Hill gap tail. No initial physical regularity is assumed. -/
theorem gap_closed_of_signed_finite_tail (D : GlobalRoughAbelianForwardData)
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q)
    (N : ℕ) (hN : 1 ≤ N)
    (hz : ∀ j : ℤ, N ≤ j.natAbs → (D.signed q).val j = 0) :
    ∀ n : ℕ, N ≤ n → hillHminusRealLabels q hr (2*n)=hillHminusRealLabels q hr (2*n-1) := by
  let f := fun j => (Weight.sobolev (1/2) j : ℂ)*(D.signed q).val j
  have hf (j : ℤ) (hj : f j ≠ 0) : j ∈ Finset.Icc (-(N : ℤ)) N := by
    by_contra hout
    have hab : N ≤ j.natAbs := by simp only [Finset.mem_Icc] at hout; omega
    exact hj (by dsimp only [f]; rw [hz j hab,mul_zero])
  let c : Coeff 2 := Coeff.ofFinsupp (Finsupp.onFinset (Finset.Icc (-(N : ℤ)) N) f hf)
  have he : (fun j => c j)=f := by funext j; exact Coeff.ofFinsupp_apply _ j
  have hreg : Memℓp f 2 := he ▸ lp.memℓp c
  obtain ⟨p,hp⟩ := D.exists_physical_of_signed_half_mem q hr hreg
  change hillOriginalHminusSource p.val = q at hp
  intro n hn
  have h := D.physical_gap_closed_of_signed_zero p n (by omega)
    (by rw [hp]; exact hz n (by simpa only [Int.natAbs_natCast] using hn))
  rw [←hillHminusRealLabels_original_source p] at h
  simpa only [hp] using h

/-- Actual real mean-zero rough preimages with fixed finite signed target
support and bounded native target norm lie in one H-minus-one compact set. -/
theorem exists_compact_container_of_signed_finite_tail (D : GlobalRoughAbelianForwardData)
    (N : ℕ) (hN : 1 ≤ N) (R : ℝ) :
    ∃ K : Set PeriodOneHminusOne, IsCompact K ∧
      ∀ q : PeriodOneHminusOne, IsRealPeriodOneHminusOne q → q.val 0 = 0 →
      ‖D.signed q‖ ≤ R →
      (∀ j : ℤ, N ≤ j.natAbs → (D.signed q).val j = 0) → q ∈ K := by
  let B := (2/Real.pi)*R^2+1
  obtain ⟨K,hK,hcontains⟩ := exists_compact_hillHminus_container_of_finite_ground_support
    (Finset.Icc (-(N : ℤ)) N) B (by dsimp only [B]; positivity)
  refine ⟨K,hK,?_⟩
  intro q hr hm hb hz
  obtain ⟨u,hu,hi,hn,_ht,_hl,_hr,_ha⟩ := exists_periodOneMiura_ground_factor q hr hm
  have he := D.ground_factor_norm_sq_le_signed_norm q hr hm u hu _ hi
  have hE : ‖u.val‖^2 ≤ (2/Real.pi)*R^2 := he.trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hb 2) (by positivity))
  have hub : ‖u.val‖ ≤ B := by dsimp only [B]; nlinarith [sq_nonneg (‖u.val‖-1)]
  have himage : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (‖u.val‖^2 : ℂ)) := by
    rw [←hn] at hi
    simpa only [ofReal_pow] using hi
  exact hcontains q u hub himage
    (hillMiura_gap_zero_outside_ground_tail q hr u _ hu hi N hN
      (D.gap_closed_of_signed_finite_tail q hr N hN hz))

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
