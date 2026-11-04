import NLS.KdV.HillRootCandidateUpdate

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV

variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

theorem hillAbelianCandidatePeriod_update_difference_ne_zero
    (roots : ℕ → ℝ) (hroots : roots ∈ hillGapRootBox q hq hr)
    (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (hmn : m ≠ n) (x y : ℝ) (hxy : x ≠ y) :
    hillAbelianCandidatePeriod q hq hr (Function.update roots (m-1) y) n m-
      hillAbelianCandidatePeriod q hq hr (Function.update roots (m-1) x) n m ≠ 0 := by
  let a := hillGapRootHilbertCoordinates q hq hr roots hroots
  let A := hillIntrinsicGapPeriod q hq hr m (fun E => hillAbelianRootSlope n m E a)
  let B := hillIntrinsicGapPeriod q hq hr m (fun E => hillAbelianHilbertPsi n (E,hillAbelianRootUpdate m (a,0)))
  have hA : A ≠ 0 := hillAbelianRootSlope_period_ne_zero q hq hr roots hroots n m hn hm
  have hx : hillAbelianCandidatePeriod q hq hr (Function.update roots (m-1) x) n m = (x:ℂ)*A+B := by
    rw [← hillIntrinsicGapPeriod_rootUpdate_eq_candidate_update q hq hr roots hroots n m m hm hm x]
    exact hillIntrinsicGapPeriod_rootUpdate_affine q hq hr n m hm hmn a x
  have hy : hillAbelianCandidatePeriod q hq hr (Function.update roots (m-1) y) n m = (y:ℂ)*A+B := by
    rw [← hillIntrinsicGapPeriod_rootUpdate_eq_candidate_update q hq hr roots hroots n m m hm hm y]
    exact hillIntrinsicGapPeriod_rootUpdate_affine q hq hr n m hm hmn a y
  rw [hx,hy]
  change (y:ℂ)*A+B-((x:ℂ)*A+B) ≠ 0
  rw [show (y:ℂ)*A+B-((x:ℂ)*A+B) = ((y:ℂ)-(x:ℂ))*A by ring]
  exact mul_ne_zero (sub_ne_zero.mpr (by exact_mod_cast (Ne.symm hxy))) hA

theorem hillAbelianPeriodRoot_eq_endpoint_formula
    (roots : ℕ → ℝ) (hroots : roots ∈ hillGapRootBox q hq hr)
    (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (hmn : m ≠ n) (x y : ℝ) (hxy : x ≠ y) :
    hillAbelianPeriodRoot q hq hr roots hroots n m = (x:ℂ)-((y:ℂ)-(x:ℂ))*
      hillAbelianCandidatePeriod q hq hr (Function.update roots (m-1) x) n m/
        (hillAbelianCandidatePeriod q hq hr (Function.update roots (m-1) y) n m-
          hillAbelianCandidatePeriod q hq hr (Function.update roots (m-1) x) n m) := by
  let a := hillGapRootHilbertCoordinates q hq hr roots hroots
  let A := hillIntrinsicGapPeriod q hq hr m (fun E => hillAbelianRootSlope n m E a)
  let B := hillIntrinsicGapPeriod q hq hr m (fun E => hillAbelianHilbertPsi n (E,hillAbelianRootUpdate m (a,0)))
  have hA : A ≠ 0 := hillAbelianRootSlope_period_ne_zero q hq hr roots hroots n m hn hm
  have hx : hillAbelianCandidatePeriod q hq hr (Function.update roots (m-1) x) n m = (x:ℂ)*A+B := by
    rw [← hillIntrinsicGapPeriod_rootUpdate_eq_candidate_update q hq hr roots hroots n m m hm hm x]
    exact hillIntrinsicGapPeriod_rootUpdate_affine q hq hr n m hm hmn a x
  have hy : hillAbelianCandidatePeriod q hq hr (Function.update roots (m-1) y) n m = (y:ℂ)*A+B := by
    rw [← hillIntrinsicGapPeriod_rootUpdate_eq_candidate_update q hq hr roots hroots n m m hm hm y]
    exact hillIntrinsicGapPeriod_rootUpdate_affine q hq hr n m hm hmn a y
  simp_rw [hx,hy]
  change -B/A = (x:ℂ)-((y:ℂ)-(x:ℂ))*((x:ℂ)*A+B)/((y:ℂ)*A+B-((x:ℂ)*A+B))
  rw [show (y:ℂ)*A+B-((x:ℂ)*A+B) = ((y:ℂ)-(x:ℂ))*A by ring]
  have hd : (y:ℂ)-(x:ℂ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (Ne.symm hxy))
  field_simp
  ring

theorem continuous_hillAbelianCandidatePeriod_coordinateUpdate
    (n m k : ℕ) (hm : 1 ≤ m) (hk : 1 ≤ k) (s : ℝ)
    (hs : s ∈ Icc (hillRealLabels q hq hr (2*m-1)) (hillRealLabels q hq hr (2*m))) :
    Continuous (fun roots : hillGapRootBox q hq hr =>
      hillAbelianCandidatePeriod q hq hr (Function.update roots.val (m-1) s) n k) := by
  have hC := continuous_hillAbelianCandidatePeriod q hq hr n k hk
  have hU := continuous_hillGapRootBoxCoordinateUpdate q hq hr m hm s hs
  have h := hC.comp hU
  simpa only [Function.comp_def,hillGapRootBoxCoordinateUpdate] using h

theorem continuous_hillAbelianPeriodRoot_re
    (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (hmn : m ≠ n) :
    Continuous (fun roots : hillGapRootBox q hq hr =>
      (hillAbelianPeriodRoot q hq hr roots.val roots.property n m).re) := by
  let l := hillRealLabels q hq hr (2*m-1)
  let u := hillRealLabels q hq hr (2*m)
  have horder : l ≤ u := monotone_hillRealLabels q hq hr (by omega)
  by_cases hlu : l = u
  · have he : (fun roots : hillGapRootBox q hq hr =>
        (hillAbelianPeriodRoot q hq hr roots.val roots.property n m).re) = (fun _ => l) := by
      funext roots
      have hb := hillAbelianPeriodRoot_re_mem_gap q hq hr roots.val roots.property n m hn hm hmn
      change (hillAbelianPeriodRoot q hq hr roots.val roots.property n m).re ∈ Icc l u at hb
      rw [← hlu] at hb
      exact le_antisymm hb.2 hb.1
    rw [he]
    exact continuous_const
  · let PL : hillGapRootBox q hq hr → ℂ := fun roots =>
      hillAbelianCandidatePeriod q hq hr (Function.update roots.val (m-1) l) n m
    let PU : hillGapRootBox q hq hr → ℂ := fun roots =>
      hillAbelianCandidatePeriod q hq hr (Function.update roots.val (m-1) u) n m
    have hPL : Continuous PL := continuous_hillAbelianCandidatePeriod_coordinateUpdate q hq hr n m m hm hm l ⟨le_rfl,horder⟩
    have hPU : Continuous PU := continuous_hillAbelianCandidatePeriod_coordinateUpdate q hq hr n m m hm hm u ⟨horder,le_rfl⟩
    have hd (roots : hillGapRootBox q hq hr) : PU roots-PL roots ≠ 0 :=
      hillAbelianCandidatePeriod_update_difference_ne_zero q hq hr roots.val roots.property n m hn hm hmn l u hlu
    have hc : Continuous (fun roots : hillGapRootBox q hq hr =>
        (l:ℂ)-((u:ℂ)-(l:ℂ))*PL roots/(PU roots-PL roots)) :=
      continuous_const.sub ((continuous_const.mul hPL).div (hPU.sub hPL) hd)
    apply (continuous_re.comp hc).congr
    intro roots
    exact congrArg Complex.re (hillAbelianPeriodRoot_eq_endpoint_formula q hq hr roots.val roots.property n m hn hm hmn l u hlu).symm

end NLS.KdV
