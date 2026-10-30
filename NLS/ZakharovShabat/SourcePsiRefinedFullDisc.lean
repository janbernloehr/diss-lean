import NLS.ZakharovShabat.SourcePsiMidpointDenominator
import NLS.ZakharovShabat.SourcePsiRefinedChiTail
import NLS.ZakharovShabat.SourceAngularOriginalDomain
import NLS.ZakharovShabat.SourcePsiOriginalChiMajorant
import NLS.SequenceSpaces.FiniteModification
import NLS.SequenceSpaces.RefinedOnePlusDecomposition

/-!
# Refined auxiliary bounds on the full original isolating disks

The auxiliary expansion on p.94 holds on every full open isolating disk,
including the finite central disks and the pi/4 tail disks. The estimates
use the original analytic roots and are uniform in the omitted index.
A fixed p/2 plus OnePlus decomposition of the actual disk supremum holds
locally on a common connected complex neighborhood of the real locus.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- On one neighborhood of any complex source, the actual omitted
midpoints have a common lattice denominator bound on all sufficiently
distant selected quarter-pi discs, independently of the omitted index. -/
theorem exists_local_sourcePeriodicMidpoint_quarter_lattice_separation
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∃ D : ℝ, 0 ≤ D ∧ ∃ K : ℕ, ∀ ψ ∈ V,
        ‖sourcePeriodicMidpointDisplacement hp hp1 ψ‖ ≤ D ∧
        ∀ m : ℤ, K ≤ m.natAbs → ∀ n : ℤ, n ≠ m →
          ∀ z ∈ closedBall ((Real.pi : ℂ)*m) (Real.pi/4),
            (Real.pi/2)*|((n-m : ℤ) : ℝ)| ≤
              ‖sourceStandardRootMidpoint hp hp1 ψ n-z‖ := by
  obtain ⟨N,hN,V,hVopen,hφV,D,hD,hdata⟩ :=
    exists_uniform_small_sourcePeriodicMidpointDisplacement hp hp1 φ
      (by positivity : 0 < Real.pi/4)
  obtain ⟨L,hL⟩ := exists_nat_gt (2*(D+Real.pi/4)/Real.pi)
  have hLπ : 2*(D+Real.pi/4) ≤ Real.pi*(L : ℝ) := by
    have h := (div_lt_iff₀ Real.pi_pos).mp hL
    nlinarith
  refine ⟨V,hVopen,hφV,D,hD,N+L,?_⟩
  intro ψ hψ
  obtain ⟨hbound,htail⟩ := hdata ψ hψ
  refine ⟨hbound,?_⟩
  intro m hm n hnm z hz
  have hpoint : ‖sourceStandardRootMidpoint hp hp1 ψ n-(Real.pi : ℂ)*n‖ ≤ D := by
    have h := (lp.norm_apply_le_norm (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
      (sourcePeriodicMidpointDisplacement hp hp1 ψ) n).trans hbound
    simpa only [sourcePeriodicMidpointDisplacement_apply,sourceStandardRootMidpoint] using h
  apply shifted_root_free_disc_distance_lower n m _ _ ?_ z hz
  by_cases hn : N < n.natAbs
  · have hnot : n ∉ Finset.Icc (-(N : ℤ)) N := by
      simp only [Finset.mem_Icc]
      omega
    have hsmall : ‖sourceStandardRootMidpoint hp hp1 ψ n-(Real.pi : ℂ)*n‖ ≤ Real.pi/4 := by
      have h := (lp.norm_apply_le_norm (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
        (sourcePeriodicMidpointDisplacement hp hp1 ψ-
          Coeff.truncate (Finset.Icc (-(N : ℤ)) N)
            (sourcePeriodicMidpointDisplacement hp hp1 ψ)) n).trans (htail N le_rfl)
      simpa only [lp.coeFn_sub,Pi.sub_apply,Coeff.truncate_apply,if_neg hnot,sub_zero,
        sourcePeriodicMidpointDisplacement_apply,sourceStandardRootMidpoint] using h
    have hd : 1 ≤ |((n-m : ℤ) : ℝ)| := by
      exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hnm)
    nlinarith [Real.pi_pos]
  · have htri : m.natAbs ≤ (m-n).natAbs+n.natAbs := by
      simpa only [sub_add_cancel] using Int.natAbs_add_le (m-n) n
    have hdist : L ≤ (n-m).natAbs := by
      have heq : (m-n).natAbs = (n-m).natAbs := by
        rw [← Int.natAbs_neg (n-m),neg_sub]
      rw [heq] at htri
      omega
    have habs : (L : ℝ) ≤ |((n-m : ℤ) : ℝ)| := by
      have hcast : (L : ℝ) ≤ ((n-m).natAbs : ℝ) := by exact_mod_cast hdist
      simpa only [Nat.cast_natAbs,Int.cast_abs] using hcast
    nlinarith [mul_le_mul_of_nonneg_left habs Real.pi_pos.le]

/-- A quotient majorant at any exponent above one gives a chi majorant
at that same exponent; it need not equal the source exponent. -/
theorem exists_sourcePsiMidpointFilledRegularFactor_refinedFullDiscTailMajorant_of_quotient
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (a : DeletedCoeff p n) (ψ : CoeffPair p)
    {r : ℝ≥0∞} [Fact (1 ≤ r)] (hr1 : 1 < r) (B : Coeff r) (D : ℝ) (hD : 0 ≤ D) (K : ℕ)
    (hmid : ‖sourceStandardRootMidpoint hp hp1 ψ n-(Real.pi : ℂ)*n‖ ≤ D)
    (hsep : ∀ m : ℤ, K ≤ m.natAbs → m ≠ n →
      ∀ z ∈ ball ((Real.pi : ℂ)*m) (Real.pi/4),
        (Real.pi/2)*|((n-m : ℤ) : ℝ)| ≤ ‖sourceStandardRootMidpoint hp hp1 ψ n-z‖)
    (hquot : ∀ m : ℤ, K ≤ m.natAbs → m ≠ n →
      ∀ z ∈ ball ((Real.pi : ℂ)*m) (Real.pi/4),
        ‖sourceSingleRootQuotientJointProduct hp hp1 m
          (z,(sourcePsiFillDeletedRoot n a (sourceStandardRootMidpoint hp hp1 ψ n),ψ))-1‖ ≤ ‖B m‖) :
    ∃ E : Coeff r,
      ‖E‖ ≤ 2*‖B‖+(2/Real.pi)*(D+Real.pi/4)*‖Coeff.puncturedLattice r hr1‖ ∧
      ∀ m : ℤ, K ≤ m.natAbs → m ≠ n →
        ∀ z ∈ ball ((Real.pi : ℂ)*m) (Real.pi/4),
          ‖sourcePsiMidpointFilledRegularFactor hp hp1 n m a ψ z-I‖ ≤ ‖E m‖ := by
  let L := Coeff.shift n (Coeff.puncturedLattice r hr1)
  let c : ℝ := (2/Real.pi)*(D+Real.pi/4)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  let E : Coeff r := (2 : ℂ) • Coeff.magnitude B+(c : ℂ) • Coeff.magnitude L
  have hEpoint m : ‖E m‖ = 2*‖B m‖+c*‖L m‖ := by
    simp only [E,lp.coeFn_add,Pi.add_apply,lp.coeFn_smul,Pi.smul_apply,
      Coeff.magnitude_apply,smul_eq_mul]
    change ‖((2 : ℝ) : ℂ)*(‖B m‖ : ℂ)+(c : ℂ)*(‖L m‖ : ℂ)‖ = _
    rw [← Complex.ofReal_mul,← Complex.ofReal_mul,← Complex.ofReal_add,Complex.norm_real]
    exact Real.norm_of_nonneg (by positivity)
  refine ⟨E,?_,?_⟩
  · calc
      ‖E‖ ≤ ‖(2 : ℂ) • Coeff.magnitude B‖+‖(c : ℂ) • Coeff.magnitude L‖ := norm_add_le _ _
      _ = 2*‖B‖+c*‖Coeff.puncturedLattice r hr1‖ := by
        simp only [norm_smul,Coeff.norm_magnitude,Complex.norm_ofNat,
          Complex.norm_real,Real.norm_of_nonneg hc,L,Coeff.norm_shift]
      _ = _ := rfl
  · intro m hm hmn z hz
    have hL : ‖L m‖ = |((n-m : ℤ) : ℝ)|⁻¹ := by
      simp only [L,Coeff.shift_apply,Coeff.puncturedLattice_apply,if_neg (sub_ne_zero.mpr hmn),
        norm_inv,Complex.norm_intCast]
      simp only [Int.cast_sub,abs_sub_comm]
    rw [hEpoint,hL]
    have hB : ‖sourceSingleRootQuotientJointProduct hp hp1 m
        (z,(sourcePsiFillDeletedRoot n a (sourceStandardRootMidpoint hp hp1 ψ n),ψ))-1‖ ≤
          ‖(lp.single p m (B m) : Coeff p) m‖ := by
      simpa only [lp.single_apply,Pi.single_eq_same] using hquot m hm hmn z hz
    simpa only [c,div_eq_mul_inv,lp.single_apply,Pi.single_eq_same] using
      norm_sourcePsiMidpointFilledRegularFactor_sub_I_le hp hp1 n m hmn a ψ (lp.single p m (B m))
        D (Real.pi/4) hD (by positivity) hmid z (mem_closedBall.mpr (mem_ball.mp hz).le) (hsep m hm hmn z hz) hB

/-- The actual chi error has a locally uniform tail majorant for every
finite exponent above one and at least p/2, uniformly in the deleted index. -/
theorem SourcePsiSquaredGapComplexExtension.exists_local_refined_fullDisc_chi_tail_majorants
    {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)}
    {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 V s)
    (φ : realTypeSourceSubmodule p) (hφ : φ.val ∈ V) :
    ∃ T : Set (CoeffPair p), IsOpen T ∧ φ.val ∈ T ∧ T ⊆ V ∧ ∃ K : ℕ,
      ∀ r : ℝ≥0∞, r ≠ ⊤ → 1 < r → ENNReal.ofReal (p.toReal/2) ≤ r →
        ∃ M : ℝ, 0 ≤ M ∧ ∀ ψ ∈ T, ∀ n : ℤ, ∃ B : Coeff r, ‖B‖ ≤ M ∧
          ∀ k : ℤ, K ≤ k.natAbs → k ≠ n → ∀ z ∈ ball ((Real.pi:ℂ)*k) (Real.pi/4),
            ‖sourcePsiMidpointFilledRegularFactor hp hp1 n k (s n ψ) ψ z-Complex.I‖ ≤ ‖B k‖ := by
  obtain ⟨N,ε,_,T,hT,hφT,hTV,Kq,hNKq,hquot⟩ := hs.exists_local_refined_quotient_tail_majorants φ hφ
  obtain ⟨G,hG,hφG,D,hD,Km,hmiddata⟩ := exists_local_sourcePeriodicMidpoint_quarter_lattice_separation hp hp1 φ.val
  let K := max Km Kq
  refine ⟨T ∩ G,hT.inter hG,⟨hφT,hφG⟩,fun _ h => hTV h.1,K,?_⟩
  intro r hr hr1 hpr
  let : Fact (1 ≤ r) := ⟨hr1.le⟩
  obtain ⟨M,hM,hbound⟩ := hquot r hr hr1 hpr
  let C := 2*M+(2/Real.pi)*(D+Real.pi/4)*‖Coeff.puncturedLattice r hr1‖
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro ψ hψ n
  obtain ⟨B,hB,hBpoint⟩ := hbound ψ hψ.1 n
  obtain ⟨hmidnorm,hsep⟩ := hmiddata ψ hψ.2
  have hmid : ‖sourceStandardRootMidpoint hp hp1 ψ n-(Real.pi:ℂ)*n‖ ≤ D := by
    have h := (lp.norm_apply_le_norm (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
      (sourcePeriodicMidpointDisplacement hp hp1 ψ) n).trans hmidnorm
    simpa only [sourcePeriodicMidpointDisplacement_apply,sourceStandardRootMidpoint] using h
  obtain ⟨E,hE,hEpoint⟩ := exists_sourcePsiMidpointFilledRegularFactor_refinedFullDiscTailMajorant_of_quotient
    hp hp1 n (s n ψ) ψ hr1 B D hD K hmid
    (fun k hk hkn z hz => hsep k ((le_max_left Km Kq).trans hk) n hkn.symm z (mem_closedBall.mpr (mem_ball.mp hz).le)) (by
      intro k hk _ z hz
      have hkq : Kq ≤ k.natAbs := (le_max_right Km Kq).trans hk
      have hkn : ¬k.natAbs ≤ N := by omega
      apply hBpoint k hkq z
      simp only [sourceIsolatingDisc,if_neg hkn]
      exact mem_ball.mp hz)
  refine ⟨E,hE.trans ?_,hEpoint⟩
  dsimp only [C]
  linarith

/-- Refined chi majorants on every prescribed original disk, with one
source neighborhood before all target exponents and deleted indices. -/
theorem SourceLemma12_12Data.original_allDisk_refined_chi_errorBound
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W V : Set (CoeffPair p)}
    {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n} {D : ℤ → Set ℂ} {c : ℝ}
    (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c) (hV : IsOpen V)
    (φ : realTypeSourceSubmodule p) (hφW : φ.val ∈ W) (hφV : φ.val ∈ V) :
    ∃ T : Set (CoeffPair p), IsOpen T ∧ φ.val ∈ T ∧ T ⊆ W ∩ V ∧
      ∀ r : ℝ≥0∞, r ≠ ⊤ → 1 < r → ENNReal.ofReal (p.toReal/2) ≤ r →
        ∃ M : ℝ, 0 ≤ M ∧ ∀ ψ ∈ T, ∀ n : ℤ, ∃ B : Coeff r, ‖B‖ ≤ M ∧
          ∀ k : ℤ, k ≠ n → ∀ z ∈ D k,
            ‖sourcePsiMidpointFilledRegularFactor hp hp1 n k (s n ψ) ψ z-I‖ ≤ ‖B k‖ := by
  classical
  obtain ⟨Tt,hTt,hφt,_,Kt,htail⟩ :=
    H.angular_extension.exists_local_refined_fullDisc_chi_tail_majorants φ hφW
  obtain ⟨Tc,hTc,hφc,hTcV,C,hC,hcoarse⟩ :=
    H.previous.original_allDisk_chi_errorBound hD hV φ.val hφW hφV
  obtain ⟨Nd,hdisks⟩ := hD.tail
  let K := max Kt (Nd+1)
  let F := Finset.Icc (-(K:ℤ)) (K:ℤ)
  refine ⟨Tt ∩ Tc,hTt.inter hTc,⟨hφt,hφc⟩,fun _ h => hTcV h.2,?_⟩
  intro r hr hr1 hpr
  let : Fact (1 ≤ r) := ⟨hr1.le⟩
  let A : Coeff r := ⟨fun k => if k ∈ F then (C:ℂ) else 0,
    memℓp_of_eq_outside_finset (lp.memℓp (0 : Coeff r)) F (by intro k hk; simp [hk])⟩
  obtain ⟨M,hM,hrows⟩ := htail r hr hr1 hpr
  refine ⟨M+‖A‖,by positivity,?_⟩
  intro ψ hψ n
  obtain ⟨Bt,hBt,hBtpoint⟩ := hrows ψ hψ.1 n
  obtain ⟨Bc,hBc,hBcpoint⟩ := hcoarse ψ hψ.2 n
  let B : Coeff r := Coeff.magnitude Bt+Coeff.magnitude A
  have hBpoint (k : ℤ) : ‖B k‖ = ‖Bt k‖+‖A k‖ := by
    simp only [B,lp.coeFn_add,Pi.add_apply,Coeff.magnitude_apply,← Complex.ofReal_add,
      Complex.norm_real,Real.norm_of_nonneg (by positivity : 0 ≤ ‖Bt k‖+‖A k‖)]
  refine ⟨B,?_,?_⟩
  · exact (norm_add_le (Coeff.magnitude Bt) (Coeff.magnitude A)).trans
      (by simpa only [Coeff.norm_magnitude] using add_le_add hBt (le_refl ‖A‖))
  · intro k hkn z hz
    rw [hBpoint]
    by_cases hk : K ≤ k.natAbs
    · have hkt : Kt ≤ k.natAbs := (le_max_left _ _).trans hk
      have hkd : Nd < k.natAbs := by have h := (le_max_right Kt (Nd+1)).trans hk; omega
      have hzball : z ∈ ball ((Real.pi:ℂ)*k) (Real.pi/4) := by
        simpa only [hdisks k hkd,refinedResonantDisk] using hz
      exact (hBtpoint k hkt hkn z hzball).trans (le_add_of_nonneg_right (norm_nonneg _))
    · have hkF : k ∈ F := by simp only [F,Finset.mem_Icc]; omega
      have hAk : ‖A k‖ = C := by
        simp only [A,if_pos hkF,Complex.norm_real,Real.norm_of_nonneg hC]
      rw [hAk]
      exact ((hBcpoint k hkn z hz).trans
        ((lp.norm_apply_le_norm (zero_lt_one.trans hp1).ne' Bc k).trans hBc)).trans
          (le_add_of_nonneg_left (norm_nonneg _))

/-- The full-disk supremum of the actual chi error, set to zero at the
omitted diagonal. Its disk and root family do not depend on an exponent. -/
def sourcePsiChiDiscSup (hp : p ≠ ⊤) (hp1 : 1 < p) (D : ℤ → Set ℂ)
    (s : (n : ℤ) → CoeffPair p → DeletedCoeff p n) (ψ : CoeffPair p) (n k : ℤ) : ℝ :=
  if k = n then 0 else
    sSup ((fun z => ‖sourcePsiMidpointFilledRegularFactor hp hp1 n k (s n ψ) ψ z-I‖) '' D k)

/-- A disk majorant bounds the actual supremum and every point of the disk. -/
theorem sourcePsiChiDiscSup_bounds (hp : p ≠ ⊤) (hp1 : 1 < p) (D : ℤ → Set ℂ)
    (s : (n : ℤ) → CoeffPair p → DeletedCoeff p n) (ψ : CoeffPair p) (n : ℤ)
    (hD : ∀ k, (D k).Nonempty) {r : ℝ≥0∞} (B : Coeff r)
    (hb : ∀ k, k ≠ n → ∀ z ∈ D k,
      ‖sourcePsiMidpointFilledRegularFactor hp hp1 n k (s n ψ) ψ z-I‖ ≤ ‖B k‖) :
    ∀ k, 0 ≤ sourcePsiChiDiscSup hp hp1 D s ψ n k ∧
      sourcePsiChiDiscSup hp hp1 D s ψ n k ≤ ‖B k‖ ∧
      (k ≠ n → ∀ z ∈ D k,
        ‖sourcePsiMidpointFilledRegularFactor hp hp1 n k (s n ψ) ψ z-I‖ ≤
          sourcePsiChiDiscSup hp hp1 D s ψ n k) := by
  intro k
  by_cases hkn : k = n
  · simp only [sourcePsiChiDiscSup,if_pos hkn]
    exact ⟨le_rfl,norm_nonneg _,fun h => (h hkn).elim⟩
  · have hbounded : BddAbove ((fun z =>
        ‖sourcePsiMidpointFilledRegularFactor hp hp1 n k (s n ψ) ψ z-I‖) '' D k) := by
      refine ⟨‖B k‖,?_⟩
      rintro y ⟨z,hz,rfl⟩
      exact hb k hkn z hz
    have hpoint : ∀ z ∈ D k,
        ‖sourcePsiMidpointFilledRegularFactor hp hp1 n k (s n ψ) ψ z-I‖ ≤
          sourcePsiChiDiscSup hp hp1 D s ψ n k := by
      intro z hz
      simpa only [sourcePsiChiDiscSup,if_neg hkn] using le_csSup hbounded ⟨z,hz,rfl⟩
    obtain ⟨z,hz⟩ := hD k
    refine ⟨(norm_nonneg _).trans (hpoint z hz),?_,fun _ => hpoint⟩
    simp only [sourcePsiChiDiscSup,if_neg hkn]
    apply csSup_le ((hD k).image _)
    rintro y ⟨w,hw,rfl⟩
    exact hb k hkn w hw

/-- A fixed p/2 plus OnePlus decomposition of the full-disk supremum,
with all source and deleted-index bounds chosen before each projection. -/
def SourcePsiFullDiscChiMixedBound (hp : p ≠ ⊤) (hp1 : 1 < p)
    (T : Set (CoeffPair p)) (D : ℤ → Set ℂ)
    (s : (n : ℤ) → CoeffPair p → DeletedCoeff p n) : Prop :=
      ∃ a : CoeffPair p × ℤ → Coeff (ENNReal.ofReal (p.toReal/2)),
      ∃ b : CoeffPair p × ℤ → CoeffOnePlus,
        (∀ ψ ∈ T, ∀ n k, (sourcePsiChiDiscSup hp hp1 D s ψ n k : ℂ) =
          a (ψ,n) k + (b (ψ,n)).1 k) ∧
        (∀ ψ ∈ T, ∀ n k, k ≠ n → ∀ z ∈ D k,
          ‖sourcePsiMidpointFilledRegularFactor hp hp1 n k (s n ψ) ψ z-I‖ ≤
            sourcePsiChiDiscSup hp hp1 D s ψ n k) ∧
        (∃ C : ℝ, 0 ≤ C ∧ ∀ ψ ∈ T, ∀ n, ‖a (ψ,n)‖ ≤ C) ∧
        ∀ (q : ℝ≥0∞) (hq1 : 1 < q) (hq : q ≠ ⊤),
          ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ ∈ T, ∀ n,
            ‖CoeffOnePlus.toCoeff q hq1 hq (b (ψ,n))‖ ≤ C

/-- The literal mixed bound for the full original-disk suprema. Both
summands are fixed before all OnePlus projection exponents, with norm
bounds uniform over the deleted index and the complex source neighborhood. -/
theorem SourceLemma12_12Data.original_allDisk_chi_sup_mixed
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W V : Set (CoeffPair p)}
    {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n} {D : ℤ → Set ℂ} {c : ℝ}
    (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c) (hV : IsOpen V)
    (φ : realTypeSourceSubmodule p) (hφW : φ.val ∈ W) (hφV : φ.val ∈ V) :
    ∃ T : Set (CoeffPair p), IsOpen T ∧ φ.val ∈ T ∧ T ⊆ W ∩ V ∧
      SourcePsiFullDiscChiMixedBound hp hp1 T D s := by
  obtain ⟨T,hT,hφT,hTV,hbound⟩ := H.original_allDisk_refined_chi_errorBound hD hV φ hφW hφV
  have hne (k : ℤ) : (D k).Nonempty := by
    obtain ⟨a,r,hr,he⟩ := hD.discs k
    rw [he]
    exact nonempty_ball.mpr hr
  have hhalf : ENNReal.ofReal (p.toReal/2) ≤ p := by
    rw [ENNReal.ofReal_le_iff_le_toReal hp]
    linarith [ENNReal.toReal_nonneg (a := p)]
  obtain ⟨a,b,he,ha,hb⟩ := Coeff.exists_onePlus_decomposition_of_refined
    {x : CoeffPair p × ℤ | x.1 ∈ T}
    (fun x k => (sourcePsiChiDiscSup hp hp1 D s x.1 x.2 k : ℂ))
    ENNReal.ofReal_ne_top (by
      intro r hr hr1 hpr
      obtain ⟨C,hC,hrows⟩ := hbound r hr hr1 hpr
      refine ⟨C,hC,?_⟩
      intro x hx
      obtain ⟨B,hB,hpoint⟩ := hrows x.1 hx x.2
      have hsup := sourcePsiChiDiscSup_bounds hp hp1 D s x.1 x.2 hne B hpoint
      have hdom (k : ℤ) : ‖(sourcePsiChiDiscSup hp hp1 D s x.1 x.2 k : ℂ)‖ ≤ ‖B k‖ := by
        rw [Complex.norm_real,Real.norm_of_nonneg (hsup k).1]
        exact (hsup k).2.1
      let b : Coeff r := ⟨fun k => (sourcePsiChiDiscSup hp hp1 D s x.1 x.2 k : ℂ),
        (lp.memℓp B).mono' hdom⟩
      refine ⟨b,fun _ => rfl,?_⟩
      exact (lp.norm_mono (zero_lt_one.trans hr1).ne' hdom).trans hB)
  refine ⟨T,hT,hφT,hTV,a,b,fun ψ hψ n k => he (ψ,n) hψ k,?_,?_,?_⟩
  · obtain ⟨_,_,hrows⟩ := hbound p hp hp1 hhalf
    intro ψ hψ n
    obtain ⟨B,_,hpoint⟩ := hrows ψ hψ n
    exact fun k => (sourcePsiChiDiscSup_bounds hp hp1 D s ψ n hne B hpoint k).2.2
  · obtain ⟨C,hC,ha⟩ := ha
    exact ⟨C,hC,fun ψ hψ n => ha (ψ,n) hψ⟩
  · intro q hq1 hq
    obtain ⟨C,hC,hb⟩ := hb q hq1 hq
    exact ⟨C,hC,fun ψ hψ n => hb (ψ,n) hψ⟩

/-- A common connected complex neighborhood of the entire real locus
carries the full original-disk mixed estimates locally. It lies inside
any prescribed open neighborhood, with the original analytic root family. -/
theorem SourceLemma12_12Data.exists_original_allDisk_chi_mixed_neighborhood
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
    {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (hrealW : realTypeSourceLocus p ⊆ W)
    (V : Set (CoeffPair p)) (hV : IsOpen V) (hrealV : realTypeSourceLocus p ⊆ V) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ IsConnected U ∧ realTypeSourceLocus p ⊆ U ∧ U ⊆ W ∩ V ∧
      ∀ ψ ∈ U, ∃ T : Set (CoeffPair p), IsOpen T ∧ ψ ∈ T ∧ T ⊆ U ∧
        ∃ D : ℤ → Set ℂ, ∃ c : ℝ, SourceIsolatingNeighborhoods hp hp1 T D c ∧
          SourcePsiFullDiscChiMixedBound hp hp1 T D s := by
  classical
  have hloc (φ : realTypeSourceLocus p) :
      ∃ T : Set (CoeffPair p), IsOpen T ∧ φ.val ∈ T ∧ T ⊆ W ∧
        ∃ D : ℤ → Set ℂ, ∃ c : ℝ, SourceIsolatingNeighborhoods hp hp1 T D c ∧
          SourcePsiFullDiscChiMixedBound hp hp1 T D s := by
    obtain ⟨N,ε,_,_,O,hO,_,hφO,c,hD⟩ :=
      exists_local_source_quantitative_isolating_discs hp hp1 φ.val φ.property
    obtain ⟨T,hT,hφT,hTO,hbound⟩ := H.original_allDisk_chi_sup_mixed hD hO
      ⟨φ.val,φ.property⟩ (hrealW φ.property) hφO
    refine ⟨T,hT,hφT,fun _ h => (hTO h).1,_,c,?_,hbound⟩
    exact { hD with
      cluster := fun ψ hψ => hD.cluster ψ (hTO hψ).2
      gap := fun ψ hψ => hD.gap ψ (hTO hψ).2 }
  choose T hT hφT hTW D c hD hb using hloc
  let S := (⋃ φ : realTypeSourceLocus p, T φ) ∩ V
  have hS : IsOpen S := (isOpen_iUnion hT).inter hV
  have hrealS : realTypeSourceLocus p ⊆ S := fun φ hφ =>
    ⟨mem_iUnion.mpr ⟨⟨φ,hφ⟩,hφT _⟩,hrealV hφ⟩
  let U := connectedComponentIn S (0 : CoeffPair p)
  have hzero : (0 : CoeffPair p) ∈ realTypeSourceLocus p := by simp [realTypeSourceLocus]
  have hrealU : realTypeSourceLocus p ⊆ U :=
    isConnected_realTypeSourceLocus.isPreconnected.subset_connectedComponentIn hzero hrealS
  have hUS : U ⊆ S := connectedComponentIn_subset _ _
  have hU : IsOpen U := hS.connectedComponentIn
  refine ⟨U,hU,isConnected_connectedComponentIn_iff.mpr (hrealS hzero),hrealU,?_,?_⟩
  · intro ψ hψ
    obtain ⟨φ,hψT⟩ := mem_iUnion.mp (hUS hψ).1
    exact ⟨hTW φ hψT,(hUS hψ).2⟩
  · intro ψ hψ
    obtain ⟨φ,hψT⟩ := mem_iUnion.mp (hUS hψ).1
    refine ⟨T φ ∩ U,(hT φ).inter hU,⟨hψT,hψ⟩,fun _ h => h.2,D φ,c φ,?_,?_⟩
    · exact { hD φ with
        cluster := fun χ hχ => (hD φ).cluster χ hχ.1
        gap := fun χ hχ => (hD φ).gap χ hχ.1 }
    · obtain ⟨a,b,he,hpoint,ha,hb⟩ := hb φ
      refine ⟨a,b,fun χ hχ => he χ hχ.1,fun χ hχ => hpoint χ hχ.1,?_,?_⟩
      · obtain ⟨C,hC,ha⟩ := ha
        exact ⟨C,hC,fun χ hχ => ha χ hχ.1⟩
      · intro q hq1 hq
        obtain ⟨C,hC,hb⟩ := hb q hq1 hq
        exact ⟨C,hC,fun χ hχ => hb χ hχ.1⟩

end NLS.ZakharovShabat
