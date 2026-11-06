import NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianInjective
import NLS.SequenceSpaces.DeletedSymmetricTruncation

/-! # Strong physical approximations by literal truncations of the rough target -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.KdV
open NLS.Articles.KdVKdV2Frequencies

/-- Every real mean-zero rough source admits actual physical mean-zero L2
approximants converging strongly in Hminus1. Their SAME global signed
coordinates are eventually the literal symmetric finite truncations. -/
theorem exists_physical_approximation_with_signed_truncations
    (D : GlobalRoughAbelianForwardData) (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (hm : q.val 0 = 0) :
    ∃ p : ℕ → hillRealMeanZeroSourceSubmodule,
      Tendsto (fun N => hillOriginalHminusSource (p N).val.val) atTop (𝓝 q) ∧
      ∀ᶠ N : ℕ in atTop, D.signed (hillOriginalHminusSource (p N).val.val) =
        WeightedCoeff.truncate (Weight.sobolev (-1/2)) 2 (Finset.Icc (-(N : ℤ)) N) (D.signed q) := by
  classical
  let L := WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1))
  let a := WeightedCoeff.meanZeroWeightedProjectionCLM (Weight.sobolev (-1)) q
  have hLa : L a = q := WeightedCoeff.meanZeroWeightedLift_projection _ q hm
  have hra : IsRealPeriodOneHminusOne (L a) := by rwa [hLa]
  let z := D.meanZeroForward a
  have hJa : deletedL2Conjugation a = a :=
    (WeightedCoeff.meanZeroWeightedLift_real_iff _ (Weight.sobolev_neg (-1)) a).mp hra
  have hJz : deletedL2Conjugation z = z := by
    change deletedL2Conjugation (D.meanZeroForward a) = D.meanZeroForward a
    rw [←D.meanZeroForward_conjugation,hJa]
  obtain ⟨U,hU,hzU,G,hG,hGa,hd⟩ := D.exists_real_weak_inverse_germ a hra
  have hGz : G z = a := hGa
  let c : ℕ → DeletedCoeff 2 0 := fun N => deletedSymmetricTruncate N z
  have ht : Tendsto c atTop (𝓝 z) := tendsto_deletedSymmetricTruncate z
  have hnear : ∀ᶠ N in atTop, c N ∈ U := ht.eventually (hU.mem_nhds hzU)
  have hphys (N : ℕ) (hN : c N ∈ U) :
      ∃ p : hillRealMeanZeroSourceSubmodule, hillOriginalHminusSource p.val.val = L (G (c N)) := by
    have hQr := (hd _ hN).2.2.2 (deletedSymmetricTruncate_real N z hJz)
    have hQm : (L (G (c N))).val 0 = 0 := WeightedCoeff.meanZeroWeightedLift_zero _ _
    have hreg : Memℓp (fun j => (Weight.sobolev (1/2) j : ℂ)*
        (D.signed (L (G (c N)))).val j) 2 := by
      rw [(hd _ hN).2.2.1]
      exact deletedSymmetricTruncate_weighted_mem _ z _ _
    have hL2 := (D.sobolev_iff_signed_mem _ hQr 0 (by norm_num)).mpr
      (by simpa only [zero_add] using hreg)
    exact exists_original_physical_meanZero_of_real_hminus_l2 _ hQr hQm
      (by simpa only [Weight.sobolev_zero_apply,ofReal_one,one_mul] using hL2)
  let p : ℕ → hillRealMeanZeroSourceSubmodule := fun N =>
    if hN : c N ∈ U then (hphys N hN).choose else 0
  have hp (N : ℕ) (hN : c N ∈ U) : hillOriginalHminusSource (p N).val.val = L (G (c N)) := by
    dsimp only [p]
    rw [dif_pos hN]
    exact (hphys N hN).choose_spec
  have hQ : Tendsto (fun N => L (G (c N))) atTop (𝓝 q) := by
    have h := L.continuous.continuousAt.tendsto.comp (((hG z hzU).continuousAt.tendsto).comp ht)
    simpa only [hGz,hLa,Function.comp_def] using h
  refine ⟨p,hQ.congr' (hnear.mono fun N hN => (hp N hN).symm),?_⟩
  have hzL : WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1/2)) z = D.signed q := by
    change WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1/2))
      (WeightedCoeff.meanZeroWeightedProjectionCLM (Weight.sobolev (-1/2)) (D.signed (L a))) = _
    rw [hLa,WeightedCoeff.meanZeroWeightedLift_projection _ _ (D.signed_zero q (D.real_mem_domain q hr))]
  filter_upwards [hnear] with N hN
  rw [hp N hN,(hd _ hN).2.2.1,meanZeroWeightedLift_deletedSymmetricTruncate,hzL]

/-- Literal signed truncation also truncates the canonically oriented
positive coordinates, with no changes to their scale or phase. -/
theorem positive_apply_of_signed_truncation
    (D : GlobalRoughAbelianForwardData) (q p : PeriodOneHminusOne)
    (hq : IsRealPeriodOneHminusOne q) (hp : IsRealPeriodOneHminusOne p)
    (N : ℕ) (he : D.signed p = WeightedCoeff.truncate (Weight.sobolev (-1/2)) 2
      (Finset.Icc (-(N : ℤ)) N) (D.signed q)) (n : ℕ+) :
    D.positive p (n : ℤ) = if (n : ℕ) ≤ N then D.positive q (n : ℤ) else 0 := by
  have hn : (0 : ℤ) < n := by exact_mod_cast n.pos
  have hh := congrArg (fun b : WeightedCoeff (Weight.sobolev (-1/2)) 2 => b.val (n : ℤ)) he
  rw [D.signed_positive_real p hp _ hn,WeightedCoeff.truncate_apply,
    D.signed_positive_real q hq _ hn] at hh
  have hi : (n : ℤ) ∈ Finset.Icc (-(N : ℤ)) N ↔ (n : ℕ) ≤ N := by
    simp only [Finset.mem_Icc]
    omega
  simp only [hi] at hh
  split_ifs with h
  · rw [if_pos h] at hh
    exact (div_left_inj' (Weight.complex_ne_zero _ _)).mp hh
  · rw [if_neg h] at hh
    exact (div_eq_zero_iff.mp hh).resolve_right (Weight.complex_ne_zero _ _)

end NLS.KdV
