import NLS.KdV.HillHminusOneGapMajorant
import NLS.KdV.HillHminusOneArnoldGapUpperBound

/-! # A sampled square majorant for the actual weighted Arnold actions

The source action is divided by exactly 1+n, the paper's base action
weight. One locally bounded ell2 sequence controls every high weighted
action on a common complex H^-1 neighborhood.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
namespace NLS.KdV

theorem exists_hillHminus_local_weighted_arnold_majorant (q : PeriodOneHminusOne) :
    ∃ N : ℕ, ∃ V : Set PeriodOneHminusOne, ∃ g : PeriodOneHminusOne → Coeff 2, ∃ B C : ℝ,
      0 < N ∧ IsOpen V ∧ q ∈ V ∧ 0 ≤ B ∧ 0 ≤ C ∧
      ∀ a ∈ V, ‖g a‖ ≤ B ∧ ∀ n : ℕ+, N ≤ (n : ℕ) →
        ‖hillHminusHighContourMoment (n : ℕ) 0 a‖/(1+(n : ℝ)) ≤ C*‖g a (n : ℤ)‖^2 := by
  obtain ⟨Ng,Vg,g,B,hNg,hVg,hqg,hB,hg⟩ := exists_hillHminus_local_l2_gap_majorant q
  obtain ⟨r,C,Na,Va,_,hC,hNa,hVa,hqa,ha⟩ := exists_hillHminus_high_arnold_gap_upper_bounds q
  refine ⟨max Ng Na,Vg ∩ Va,g,B,C*(3*Real.pi)^2,
    hNg.trans_le (le_max_left _ _),hVg.inter hVa,⟨hqg,hqa⟩,hB,by positivity,?_⟩
  intro a hac
  refine ⟨(hg a hac.1).1,?_⟩
  intro n hn
  have hnG : Ng ≤ (n : ℕ) := (le_max_left Ng Na).trans hn
  have hnA : Na ≤ (n : ℕ) := (le_max_right Ng Na).trans hn
  obtain ⟨l,u,hpair,hbound⟩ := ha n hnA a hac.2
  have hgap := (hg a hac.1).2 n hnG r l u hpair
  have hnpos : (0 : ℝ) < (n : ℕ) := by positivity
  have hfactor : (n : ℝ)/(1+(n : ℝ)) ≤ 1 := by
    apply (div_le_one (by positivity : 0 < 1+(n : ℝ))).mpr
    linarith
  calc
    _ ≤ (C*‖l-u‖^2/(n : ℕ))/(1+(n : ℝ)) := by gcongr
    _ ≤ (C*((3*Real.pi)*(n : ℕ)*‖g a (n : ℤ)‖)^2/(n : ℕ))/(1+(n : ℝ)) := by gcongr
    _ = (C*(3*Real.pi)^2*‖g a (n : ℤ)‖^2)*((n : ℝ)/(1+(n : ℝ))) := by
      field_simp [hnpos.ne']
    _ ≤ C*(3*Real.pi)^2*‖g a (n : ℤ)‖^2 :=
      mul_le_of_le_one_right (by positivity) hfactor

end NLS.KdV
