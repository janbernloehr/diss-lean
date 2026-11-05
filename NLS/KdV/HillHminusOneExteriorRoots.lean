import NLS.KdV.HillHminusOneDiscAsymptotics
import NLS.KdV.HillHminusOneReality
import NLS.KdV.HillFreeSpectrum

/-! # Exterior confinement of every actual H^-1 characteristic root

The Miura chart identifies the actual Hill radicand with the original
NLS periodic product at the translated square-root energy. Its uniform
exterior product estimate confines every root, including roots outside
the already constructed high discs. No bound on an L2 approximation is
used.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.KdV

theorem exists_hillHminus_chart_frequency_root_confinement
    (C : HillHminusMiuraChart) (q : PeriodOneHminusOne) (hq : q ∈ C.domain)
    (r : ℝ) (hr : 0 < r) (hrpi : r ≤ Real.pi/4) :
    ∃ V : Set PeriodOneHminusOne, IsOpen V ∧ q ∈ V ∧ V ⊆ C.domain ∧
      ∃ R : ℝ, 0 < R ∧ ∀ a ∈ V, ∀ lambda : ℂ, hillHminusRadicand a lambda = 0 →
        ‖sqrt (lambda+C.energyShift)‖ < R ∨
          ∃ k : ℤ, ‖sqrt (lambda+C.energyShift)-(Real.pi : ℂ)*k‖ < r := by
  let psi : PeriodOneHminusOne → PairSpace 2 := fun a =>
    periodOnePotential (hillMiuraDiagonal (C.lift a))
  have hpsi : AnalyticOnNhd ℂ psi C.domain := by
    intro a ha
    exact ((periodOnePotential (p := 2)).analyticAt _).comp
      ((hillMiuraDiagonal.analyticAt _).comp (C.lift_analytic a ha))
  obtain ⟨U,hU,_,hqU,_,R0,hbound⟩ := exists_uniform_exterior_canonicalProducts
    (by simp : (2 : ℝ≥0∞) ≠ ⊤) (by norm_num) (psi q) hr hrpi (by norm_num : 0 < (1/2 : ℝ))
  let V := C.domain ∩ psi ⁻¹' U
  refine ⟨V,hpsi.continuousOn.isOpen_inter_preimage C.domain_open hU,⟨hq,hqU⟩,
    inter_subset_left,max R0 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _),?_⟩
  intro a ha lambda hzero
  let w : ℂ := sqrt (lambda+C.energyShift)
  by_cases hw : ‖w‖ < max R0 1
  · exact Or.inl hw
  right
  by_contra! hsep
  have hb := (hbound (psi a) ha.2 (periodOnePotential_mem _) w
    ((le_max_left R0 1).trans (le_of_not_gt hw)) hsep).1
  have hprod : canonicalPeriodicProduct (by simp) (psi a) w = 0 := by
    rw [canonicalPeriodic_eq_discriminant_sq_sub_four_finite (by simp) (by norm_num)
      (psi a) (periodOnePotential_mem _) w]
    have ht : hillHminusDiscriminant a lambda = canonicalDiscriminant (by simp) (psi a) w := by
      rw [hillHminusDiscriminant_eq_chart C a ha.1]
      rfl
    rw [← ht]
    exact hzero
  rw [hprod,zero_div,zero_sub,norm_neg,norm_one] at hb
  norm_num at hb

/-- A common H^-1 neighborhood confines all energy roots to a bounded
central region or explicitly translated high free-energy neighborhoods. -/
theorem exists_hillHminus_energy_root_confinement (q : PeriodOneHminusOne)
    (r : ℝ) (hr : 0 < r) (hrpi : r ≤ Real.pi/4) :
    ∃ V : Set PeriodOneHminusOne, IsOpen V ∧ q ∈ V ∧
      ∃ M A : ℝ, 0 < M ∧ 0 ≤ A ∧ ∀ a ∈ V, ∀ lambda : ℂ,
        hillHminusRadicand a lambda = 0 →
          ‖lambda‖ ≤ M ∨ ∃ n : ℕ,
            ‖lambda-(freeHillValue n : ℂ)‖ ≤ 2*Real.pi*(n : ℝ)*r+A := by
  obtain ⟨C,hqC⟩ := exists_hillHminusMiuraChart q
  obtain ⟨V,hV,hqV,_,R,hR,hroots⟩ := exists_hillHminus_chart_frequency_root_confinement C q hqC r hr hrpi
  refine ⟨V,hV,hqV,R^2+‖C.energyShift‖+1,r^2+‖C.energyShift‖,by positivity,by positivity,?_⟩
  intro a ha lambda hzero
  let w : ℂ := sqrt (lambda+C.energyShift)
  have hsq : w^2 = lambda+C.energyShift := complex_sqrt_sq _
  rcases hroots a ha lambda hzero with hw | ⟨k,hk⟩
  · left
    have he : lambda = w^2-C.energyShift := by rw [hsq]; ring
    rw [he]
    have hh := norm_sub_le (w^2) C.energyShift
    rw [norm_pow] at hh
    have hn : ‖w‖^2 ≤ R^2 := (sq_le_sq₀ (norm_nonneg _) hR.le).mpr hw.le
    linarith
  · right
    refine ⟨k.natAbs,?_⟩
    let p : ℂ := (Real.pi : ℂ)*k
    have hp : ‖p‖ = Real.pi*(k.natAbs : ℝ) := by
      simp only [p,norm_mul,norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos,norm_intCast,
        Nat.cast_natAbs,Int.cast_abs]
    have hfree : p^2 = (freeHillValue k.natAbs : ℂ) := by
      rw [freeHillValue_natAbs]
      dsimp only [p,freeHillValue]
      push_cast
      ring
    have hplus : ‖w+p‖ ≤ r+2*‖p‖ := by
      have he : w+p = (w-p)+2*p := by ring
      rw [he]
      have hh := norm_add_le (w-p) (2*p)
      have htwo : ‖(2 : ℂ)*p‖ = 2*‖p‖ := by simp
      rw [htwo] at hh
      linarith
    have he : lambda-(freeHillValue k.natAbs : ℂ) = (w-p)*(w+p)-C.energyShift := by
      rw [← hfree]
      linear_combination -hsq
    rw [he]
    calc
      _ ≤ ‖(w-p)*(w+p)‖+‖C.energyShift‖ := norm_sub_le _ _
      _ = ‖w-p‖*‖w+p‖+‖C.energyShift‖ := by rw [norm_mul]
      _ ≤ r*(r+2*‖p‖)+‖C.energyShift‖ := by
        exact add_le_add (mul_le_mul hk.le hplus (norm_nonneg _) hr.le) le_rfl
      _ = 2*Real.pi*(k.natAbs : ℝ)*r+(r^2+‖C.energyShift‖) := by rw [hp]; ring

/-- Compact sets admit one neighborhood and one pair of confinement
constants, even when their L2 representatives have unbounded norms. -/
theorem exists_hillHminus_energy_root_confinement_near_compact
    (K : Set PeriodOneHminusOne) (hK : IsCompact K)
    (r : ℝ) (hr : 0 < r) (hrpi : r ≤ Real.pi/4) :
    ∃ V : Set PeriodOneHminusOne, IsOpen V ∧ K ⊆ V ∧
      ∃ M A : ℝ, 0 < M ∧ 0 ≤ A ∧ ∀ a ∈ V, ∀ lambda : ℂ,
        hillHminusRadicand a lambda = 0 →
          ‖lambda‖ ≤ M ∨ ∃ n : ℕ,
            ‖lambda-(freeHillValue n : ℂ)‖ ≤ 2*Real.pi*(n : ℝ)*r+A := by
  classical
  have hl (q : K) := exists_hillHminus_energy_root_confinement q.val r hr hrpi
  choose V hV hqV M A hM hA hroots using hl
  obtain ⟨S,hS⟩ := hK.elim_finite_subcover V hV
    (fun q hq => mem_iUnion.mpr ⟨⟨q,hq⟩,hqV ⟨q,hq⟩⟩)
  refine ⟨⋃ q ∈ S, V q,isOpen_iUnion (fun q => isOpen_iUnion (fun _ => hV q)),hS,
    1+∑ q ∈ S, M q,∑ q ∈ S, A q,(by
      have hh : 0 ≤ ∑ q ∈ S, M q := Finset.sum_nonneg (fun q _ => (hM q).le)
      linarith),
    Finset.sum_nonneg (fun q _ => hA q),?_⟩
  intro a ha lambda hzero
  obtain ⟨q,hq⟩ := mem_iUnion.mp ha
  obtain ⟨hqS,haV⟩ := mem_iUnion.mp hq
  rcases hroots q a haV lambda hzero with h | ⟨n,hn⟩
  · left
    have hh := Finset.single_le_sum (fun q _ => (hM q).le) hqS
    linarith
  · right
    refine ⟨n,hn.trans ?_⟩
    have hh := Finset.single_le_sum (fun q _ => hA q) hqS
    linarith

/-- Uniform confinement along every straight source path from a common
complex H^-1 neighborhood. The free endpoint is included. -/
theorem exists_hillHminus_source_energy_root_confinement
    (q : PeriodOneHminusOne) (r : ℝ) (hr : 0 < r) (hrpi : r ≤ Real.pi/4) :
    ∃ V : Set PeriodOneHminusOne, IsOpen V ∧ q ∈ V ∧
      ∃ M A : ℝ, 0 < M ∧ 0 ≤ A ∧ ∀ a ∈ V, ∀ s ∈ Icc (0 : ℝ) 1,
        ∀ lambda : ℂ, hillHminusRadicand ((s : ℂ) • a) lambda = 0 →
          ‖lambda‖ ≤ M ∨ ∃ n : ℕ,
            ‖lambda-(freeHillValue n : ℂ)‖ ≤ 2*Real.pi*(n : ℝ)*r+A := by
  let K : Set PeriodOneHminusOne := (fun s : ℝ => (s : ℂ) • q) '' Icc (0 : ℝ) 1
  have hK : IsCompact K := isCompact_Icc.image (by fun_prop)
  obtain ⟨U,hU,hKU,M,A,hM,hA,hroots⟩ :=
    exists_hillHminus_energy_root_confinement_near_compact K hK r hr hrpi
  let D : Set (ℂ × PeriodOneHminusOne) := univ ×ˢ U
  let V : Set PeriodOneHminusOne := (fun a => ((0 : ℂ),a)) ⁻¹' sourceSegmentDomain 0 D
  have hV : IsOpen V := (isOpen_sourceSegmentDomain 0 D (isOpen_univ.prod hU)).preimage
    (continuous_const.prodMk continuous_id)
  have hqV : q ∈ V := by
    intro s hs
    exact ⟨mem_univ _,by simpa only [sourceSegmentMap,zero_add,sub_zero] using hKU ⟨s,hs,rfl⟩⟩
  refine ⟨V,hV,hqV,M,A,hM,hA,?_⟩
  intro a ha s hs lambda hzero
  apply hroots _ ?_ lambda hzero
  simpa only [sourceSegmentMap,zero_add,sub_zero] using (ha s hs).2

end NLS.KdV
