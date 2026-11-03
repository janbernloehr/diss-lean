import NLS.KdV.HminusOneDirichletRealLabels
import NLS.KdV.HminusOneDirichletAsymptotics
import NLS.KdV.HminusOneDirichletHighGaps

/-! The ENTIRE intrinsic positive scalar Dirichlet sequence has the
original n-times-L2 asymptotic and the original high-gap location.
The central scalar labels have their proved positive index offset. -/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.KdV

/-- The full intrinsic Dirichlet labels, including central energies,
have inverse-bracket weighted L2 displacement from n²*pi² on positive indices. -/
theorem memlp_hillHminusDirichletLabels_inverseBracket_error
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) :
    Memℓp (fun n : ℕ+ => inverseBracketCoefficients (n:ℕ)*
      ((hillHminusDirichletLabels q hq n:ℂ)-((Real.pi:ℂ)*(n:ℕ))^2)) 2 := by
  obtain ⟨c,_,_,u,hi⟩ := exists_real_periodOneMiura_shift q hq 0
  have hi' : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 ((c^2:ℝ):ℂ)) :=
    by simpa only [Complex.ofReal_pow] using hi
  have h := memlp_hillMiuraDirichletEnergy_inverseBracket_error u.val ((c^2:ℝ):ℂ)
  have hInjective : Function.Injective (fun n : ℕ+ => ((n:ℕ):ℤ)) := by
    intro i j he
    exact Subtype.ext (Int.ofNat.inj he)
  have hp : Memℓp (fun n : ℕ+ => inverseBracketCoefficients (n:ℕ)*
      (hillMiuraDirichletEnergy u.val (c^2:ℝ) (n:ℕ)-((Real.pi:ℂ)*(n:ℕ))^2)) 2 := by
    apply (memℓp_gen_iff (by norm_num : 0 < (2:ℝ≥0∞).toReal)).mpr
    exact (h.summable (by norm_num)).comp_injective hInjective
  rw [hillHminusDirichletLabels_eq_miura q hq u (c^2) hi']
  convert! hp using 1
  funext n
  rw [hillMiuraDirichletEnergy_ofReal_re]

/-- The source's literal n-times-L2 asymptotic on positive indices:
the full scalar energy error divided by n belongs to L2. -/
theorem memlp_hillHminusDirichletLabels_inverseIndex_error
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) :
    Memℓp (fun n : ℕ+ =>
      ((hillHminusDirichletLabels q hq n:ℂ)-((Real.pi:ℂ)*(n:ℕ))^2)/(n:ℕ)) 2 := by
  have h := memlp_hillHminusDirichletLabels_inverseBracket_error q hq
  apply (h.norm.const_mul (2:ℝ)).mono
  intro n
  let E := (hillHminusDirichletLabels q hq n:ℂ)-((Real.pi:ℂ)*(n:ℕ))^2
  let k : ℝ := (n:ℕ)
  have hn : (1:ℕ) ≤ n.val := n.property
  have hk : (1:ℝ) ≤ k := by dsimp [k]; exact_mod_cast hn
  have hkpos : 0 < k := by linarith
  have hB : ‖inverseBracketCoefficients (n:ℕ)‖ = (1+k)⁻¹ := by
    have hb := norm_inverseBracketCoefficients_apply (n:ℕ)
    simp only [Int.cast_natCast] at hb
    rw [abs_of_nonneg (show (0:ℝ) ≤ ((n:ℕ):ℝ) from Nat.cast_nonneg _)] at hb
    exact hb
  have hineq : ‖E‖/k ≤ (2*‖E‖)/(1+k) := by
    apply (div_le_div_iff₀ hkpos (by positivity : 0 < 1+k)).mpr
    have hp := mul_nonneg (sub_nonneg.mpr hk) (norm_nonneg E)
    nlinarith
  change ‖E/(n:ℕ)‖ ≤ 2*‖inverseBracketCoefficients (n:ℕ)*E‖
  calc
    ‖E/(n:ℕ)‖ = ‖E‖/k := by rw [norm_div,Complex.norm_natCast]
    _ ≤ (2*‖E‖)/(1+k) := hineq
    _ = 2*‖inverseBracketCoefficients (n:ℕ)*E‖ := by rw [norm_mul,hB]; ring

/-- Every sufficiently high intrinsic Dirichlet label lies in the SAME
original periodic Hill gap. Its exact midpoint deviation is bounded by
half that gap, with collapsed periodic gaps included. -/
theorem exists_hillHminusDirichletLabels_in_high_gap
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ+, N ≤ (n:ℕ) →
      hillHminusLabels q hq (2*(n:ℕ)-1) ≤ hillHminusDirichletLabels q hq n ∧
      hillHminusDirichletLabels q hq n ≤ hillHminusLabels q hq (2*(n:ℕ)) ∧
      ‖(((hillHminusLabels q hq (2*(n:ℕ)-1)+hillHminusLabels q hq (2*(n:ℕ)))/2:ℝ):ℂ)-
          (hillHminusDirichletLabels q hq n:ℂ)‖ ≤
        ‖((hillHminusLabels q hq (2*(n:ℕ))-hillHminusLabels q hq (2*(n:ℕ)-1):ℝ):ℂ)‖/2 := by
  obtain ⟨c,_,_,u,hi⟩ := exists_real_periodOneMiura_shift q hq 0
  have hi' : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 ((c^2:ℝ):ℂ)) :=
    by simpa only [Complex.ofReal_pow] using hi
  obtain ⟨N,hN,hgap⟩ := exists_hillMiuraDirichletEnergy_in_high_gap q hq u (c^2) hi'
  refine ⟨N,hN,fun n hn => ?_⟩
  obtain ⟨_,_,hl,hr,hm⟩ := hgap (n:ℕ) hn
  have he : hillHminusDirichletLabels q hq n =
      (hillMiuraDirichletEnergy u.val (c^2:ℝ) (n:ℕ)).re :=
    congrFun (hillHminusDirichletLabels_eq_miura q hq u (c^2) hi') n
  rw [he,hillMiuraDirichletEnergy_ofReal_re]
  exact ⟨hl,hr,hm⟩

/-- At zero original potential the complete positive Dirichlet sequence
has exactly the source normalization n²*pi², including its first index. -/
theorem hillHminusDirichletLabels_zero
    (hq : IsRealPeriodOneHminusOne (0:PeriodOneHminusOne)) (n : ℕ+) :
    hillHminusDirichletLabels 0 hq n = (Real.pi*(n:ℝ))^2 := by
  let u : PeriodOneRealL2 := ⟨0,by intro k; simp⟩
  have hm : periodOneMiura (0:Coeff 2) = 0 := by
    apply Subtype.ext
    funext k
    rw [periodOneMiura_apply]
    simp
  have hi : periodOneMiura u.val = (0:PeriodOneHminusOne)+periodOneL2Inclusion (lp.single 2 0 (0:ℂ)) := by
    simpa only [u,lp.single_zero,map_zero,add_zero] using hm
  have he := congrFun (hillHminusDirichletLabels_eq_miura 0 hq u 0 hi) n
  rw [he]
  have hz : hillMiuraDiracDirichlet u.val (n:ℕ) = (Real.pi:ℂ)*(n:ℕ) := by
    simp only [hillMiuraDiracDirichlet,u,map_zero,
      NLS.ZakharovShabat.canonicalAuxiliaryPeriodOneRoots_zero,Int.cast_natCast]
  rw [hillMiuraDirichletEnergy,hz,Complex.ofReal_zero,sub_zero]
  simp only [pow_two,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,
    Complex.ofReal_im,Complex.natCast_re,Complex.natCast_im,mul_zero,zero_mul,add_zero,sub_zero]

end NLS.KdV
