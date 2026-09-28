import NLS.ZakharovShabat.SourcePsiGlobalHeadKernelBound
import NLS.ZakharovShabat.SourcePsiFinitePairCoordinateBound

/-!
# Uniform psi equation bounds on the finite selected head

For distant deleted indices, the selected standard-root kernel and
the weighted regular factor are bounded on every fixed head circle.
The finitely many remaining deleted indices are controlled by scalar
holomorphy on the same contour family.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- A finite head family of shifted selected discs avoids the deleted
free root once its index is sufficiently distant. -/
theorem exists_sourcePsi_headDiscs_avoid_distant_freeRoot
    (K : ℕ) (c : ℤ → ℂ) (R : ℤ → ℝ)
    (hR : ∀ m : ℤ, 0 ≤ R m) :
    ∃ N : ℕ, K < N ∧
      ∀ n : ℤ, N ≤ n.natAbs →
        ∀ m : ℤ, m.natAbs ≤ K →
          ∀ z ∈ closedBall (c m) (R m),
            z ≠ (Real.pi : ℂ)*n := by
  let s : Finset ℤ := Finset.Icc (-(K : ℤ)) (K : ℤ)
  have hRs (m : ℤ) (hm : m ∈ s) : 0 ≤ R m := hR m
  obtain ⟨L,hL⟩ := exists_uniform_shifted_disc_lattice_cutoff
    s c R hRs
  let N : ℕ := K+L+1
  refine ⟨N,(by dsimp [N]; omega),?_⟩
  intro n hn m hmK z hz
  have hm : m ∈ s := by
    simp only [s,Finset.mem_Icc]
    omega
  have htri : n.natAbs ≤ (n-m).natAbs + m.natAbs := by
    have h := Int.natAbs_add_le (n-m) m
    simpa only [sub_add_cancel] using h
  have hdist : L ≤ (n-m).natAbs := by
    dsimp [N] at hn
    omega
  have hsep := hL m hm n hdist
  have hnorm := shifted_disc_free_lattice_distance_lower
    n m (c m) (R m) hsep z hz
  have hmn : n ≠ m := by
    intro heq
    subst n
    simp only [sub_self,Int.natAbs_zero] at hdist
    have : L = 0 := by omega
    dsimp [N] at hn
    omega
  have habs : 0 < |((n-m : ℤ) : ℝ)| := by
    have h := Int.one_le_abs (sub_ne_zero.mpr hmn)
    exact_mod_cast (lt_of_lt_of_le zero_lt_one h)
  have hnormpos : 0 < ‖((Real.pi : ℂ)*n)-z‖ := by
    nlinarith [Real.pi_pos]
  exact Ne.symm (sub_ne_zero.mp (norm_pos_iff.mp hnormpos))

/-- A circle bound for the selected kernel and weighted regular factor
gives a direct bound for the corresponding psi equation coordinate. -/
theorem norm_sourcePsiEquationCoordinate_le_of_kernel_regularFactor
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n m : ℤ) (a : Coeff p) (ψ : CoeffPair p)
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hcircle : sphere c R ⊆ sourceCanonicalRootDomain hp hp1 ψ)
    (havoid : ∀ z ∈ sphere c R, z ≠ displacedRoots a n)
    (A B : ℝ) (hA : 0 ≤ A)
    (hkernel : ∀ z ∈ sphere c R,
      ‖(displacedRoots a m-z) /
        sourceStandardRoot hp hp1 ψ m z‖ ≤ A)
    (hregular : ∀ z ∈ sphere c R,
      ‖(((n-m : ℤ) : ℂ) *
        sourcePsiGapRegularFactor hp hp1 n m a ψ z)‖ ≤ B) :
    ‖sourcePsiEquationCoordinate hp hp1 n m a ψ c R‖ ≤
      2*Real.pi*R*(A*B) := by
  rw [sourcePsiEquationCoordinate_eq_gap_factor_circleIntegral
    hp hp1 n m a ψ c R hR hcircle havoid]
  rw [← circleIntegral.integral_const_mul]
  have heq :
      (∮ z in C(c,R),
        ((n-m : ℤ) : ℂ) *
          (((displacedRoots a m-z) /
            sourceStandardRoot hp hp1 ψ m z) *
            sourcePsiGapRegularFactor hp hp1 n m a ψ z)) =
      ∮ z in C(c,R),
        ((displacedRoots a m-z) /
          sourceStandardRoot hp hp1 ψ m z) *
          (((n-m : ℤ) : ℂ) *
            sourcePsiGapRegularFactor hp hp1 n m a ψ z) := by
    apply circleIntegral.integral_congr hR
    intro z _
    ring
  rw [heq]
  apply circleIntegral.norm_integral_le_of_norm_le_const hR
  intro z hz
  rw [norm_mul]
  exact mul_le_mul (hkernel z hz) (hregular z hz)
    (norm_nonneg _) hA

/-- On a common neighborhood of any real-type source, all equation
coordinates on the finite selected head circles share one bound,
uniformly in the deleted index. -/
theorem exists_local_sourcePsi_uniformHeadCoordinateBound
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (a₀ : Coeff p) (H : ℕ) :
    ∃ U : Set (Coeff p × CoeffPair p), IsOpen U ∧
      (a₀,φ) ∈ U ∧
      ∃ K : ℕ, H ≤ K ∧ ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
        (∀ m : ℤ, (c m).im = 0) ∧
        (∀ m : ℤ, K < m.natAbs →
          c m = (Real.pi : ℂ)*m ∧ R m = Real.pi/8) ∧
        (∀ t ∈ U, ∀ m : ℤ,
          0 < R m ∧
          sourcePeriodicSegment hp hp1 t.2 m ⊆ ball (c m) (R m) ∧
          closedBall (c m) (R m) ⊆
            sourceStandardRootOmittedDomain hp hp1 t.2 m ∧
          sphere (c m) (R m) ⊆
            sourceCanonicalRootDomain hp hp1 t.2) ∧
        ∃ C : ℝ, 0 ≤ C ∧
          ∀ n : ℤ, ∀ a : DeletedCoeff p n, ∀ ψ : CoeffPair p,
            ((a : Coeff p),ψ) ∈ U →
              ∀ m : ℤ, m.natAbs ≤ K →
                ‖sourcePsiEquationCoordinate hp hp1 n m
                  (a : Coeff p) ψ (c m) (R m)‖ ≤ C := by
  obtain ⟨Ureg,hUregOpen,hbaseReg,Nreg,Kreg,c,R,hcReal,hchoice,hgeom,
      Mreg,hMreg,hmajor⟩ :=
    exists_local_sourcePsi_distantDeleted_uniformRegularFactorMajorant
      hp hp1 φ hφ a₀
  let K : ℕ := max Kreg H
  have hHK : H ≤ K := le_max_right _ _
  have hchoiceK (m : ℤ) (hm : K < m.natAbs) :
      c m = (Real.pi : ℂ)*m ∧ R m = Real.pi/8 :=
    hchoice m (by dsimp [K] at hm; omega)
  let s : Finset ℤ := Finset.Icc (-(K : ℤ)) (K : ℤ)
  have hR (m : ℤ) : 0 ≤ R m := (hgeom (a₀,φ) hbaseReg m).1.le
  have hcircleBase (m : ℤ) :
      sphere (c m) (R m) ⊆ sourceCanonicalRootDomain hp hp1 φ :=
    (hgeom (a₀,φ) hbaseReg m).2.2.2
  obtain ⟨Vker,hVkerOpen,hφVker,Mker,hMker,hker⟩ :=
    exists_local_sourceStandardRoot_inv_uniformFiniteCircleBound
      hp hp1 φ hφ s c R hcircleBase
  obtain ⟨Navoid,hNavoidK,havoidFree⟩ :=
    exists_sourcePsi_headDiscs_avoid_distant_freeRoot K c R hR
  let N : ℕ := max Nreg Navoid
  let sN : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ)
  obtain ⟨Ufin,hUfinOpen,hbaseFin,Mfin,hMfin,hfin⟩ :=
    exists_local_sourcePsi_uniformFinitePairCoordinateBound
      hp hp1 φ hφ sN s c R hR hcircleBase a₀
  let U : Set (Coeff p × CoeffPair p) :=
    Ureg ∩ Ufin ∩ (ball a₀ 1 ×ˢ Vker)
  have hUopen : IsOpen U :=
    (hUregOpen.inter hUfinOpen).inter (isOpen_ball.prod hVkerOpen)
  have hbase : (a₀,φ) ∈ U :=
    ⟨⟨hbaseReg,hbaseFin⟩,mem_ball_self (by norm_num),hφVker⟩
  let T : ℝ := ‖a₀‖+1
  let D : ℝ := ∑ m ∈ s, (‖((Real.pi : ℂ)*m)-c m‖+R m)
  let S : ℝ := ∑ m ∈ s, R m
  let A : ℝ := (T+D)*Mker
  let B : ℝ := (2/Real.pi)*(1+Mreg)
  let Cdist : ℝ := 2*Real.pi*S*(A*B)
  let C : ℝ := max Mfin Cdist
  have hD : 0 ≤ D := Finset.sum_nonneg (fun m _ =>
    add_nonneg (norm_nonneg _) (hR m))
  have hS : 0 ≤ S := Finset.sum_nonneg (fun m _ => hR m)
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hCdist : 0 ≤ Cdist := by dsimp [Cdist]; positivity
  have hC : 0 ≤ C := le_max_of_le_left hMfin
  refine ⟨U,hUopen,hbase,K,hHK,c,R,hcReal,hchoiceK,?_,C,hC,?_⟩
  · intro t ht m
    exact hgeom t ht.1.1 m
  intro n a ψ hpair m hmK
  have hm : m ∈ s := by
    simp only [s,Finset.mem_Icc]
    omega
  obtain ⟨⟨hreg,hfinite⟩,haBall,hψker⟩ := hpair
  by_cases hn : N ≤ n.natAbs
  · have hnReg : Nreg ≤ n.natAbs := by dsimp [N] at hn; omega
    have hnAvoid : Navoid ≤ n.natAbs := by dsimp [N] at hn; omega
    have hmn : m ≠ n := by
      intro heq
      subst n
      dsimp [N] at hn
      omega
    obtain ⟨Q,hQnorm,hQ⟩ := hmajor n hnReg a ψ hreg
    have hQcoord : ‖Q m‖ ≤ Mreg :=
      (lp.norm_apply_le_norm
        (ne_of_gt (zero_lt_one.trans_le Fact.out)) Q m).trans hQnorm
    have ha : ‖(a : Coeff p)‖ ≤ T := by
      have hdist : ‖(a : Coeff p)-a₀‖ < 1 := by
        simpa only [mem_ball,dist_eq_norm] using haBall
      have hsum : ‖(a : Coeff p)‖ ≤ ‖a₀‖+
          ‖(a : Coeff p)-a₀‖ := by
        have heq : (a : Coeff p) = a₀+((a : Coeff p)-a₀) := by abel
        calc
          ‖(a : Coeff p)‖ = ‖a₀+((a : Coeff p)-a₀)‖ :=
            congrArg norm heq
          _ ≤ _ := norm_add_le _ _
      dsimp [T]
      linarith
    have hacoord : ‖(a : Coeff p) m‖ ≤ T :=
      (lp.norm_apply_le_norm
        (ne_of_gt (zero_lt_one.trans_le Fact.out)) (a : Coeff p) m).trans ha
    have hDm : ‖((Real.pi : ℂ)*m)-c m‖+R m ≤ D :=
      Finset.single_le_sum (f := fun k =>
        ‖((Real.pi : ℂ)*k)-c k‖+R k)
        (fun k hk => add_nonneg (norm_nonneg _) (hR k)) hm
    have hSm : R m ≤ S :=
      Finset.single_le_sum (f := R) (fun k hk => hR k) hm
    have hkernel (z : ℂ) (hz : z ∈ sphere (c m) (R m)) :
        ‖(displacedRoots (a : Coeff p) m-z) /
          sourceStandardRoot hp hp1 ψ m z‖ ≤ A := by
      have hzR : ‖c m-z‖ = R m := by
        simpa only [dist_eq_norm,norm_sub_rev] using (mem_sphere.mp hz)
      have hzc : ‖((Real.pi : ℂ)*m)-z‖ ≤
          ‖((Real.pi : ℂ)*m)-c m‖+R m := by
        have heq : ((Real.pi : ℂ)*m)-z =
            (((Real.pi : ℂ)*m)-c m)+(c m-z) := by ring
        rw [heq]
        simpa only [hzR] using norm_add_le
          (((Real.pi : ℂ)*m)-c m) (c m-z)
      have hnum : ‖displacedRoots (a : Coeff p) m-z‖ ≤ T+D := by
        have heq : displacedRoots (a : Coeff p) m-z =
            (a : Coeff p) m+(((Real.pi : ℂ)*m)-z) := by
          simp only [displacedRoots]
          ring
        rw [heq]
        have htri := norm_add_le ((a : Coeff p) m)
          (((Real.pi : ℂ)*m)-z)
        linarith
      rw [div_eq_mul_inv,norm_mul]
      exact mul_le_mul hnum (hker ψ hψker m hm z hz)
        (norm_nonneg _) (add_nonneg hT hD)
    have hregular (z : ℂ) (hz : z ∈ sphere (c m) (R m)) :
        ‖(((n-m : ℤ) : ℂ) *
          sourcePsiGapRegularFactor hp hp1 n m
            (a : Coeff p) ψ z)‖ ≤ B := by
      have hq := hQ m hmn z (sphere_subset_closedBall hz)
      dsimp [B]
      have hq' : 1+‖Q m‖ ≤ 1+Mreg := by linarith
      exact hq.trans (mul_le_mul_of_nonneg_left
        hq' (by positivity))
    have hrootn : displacedRoots (a : Coeff p) n =
        (Real.pi : ℂ)*n := by
      have haN : (a : Coeff p) n = 0 := a.property
      simp [displacedRoots,haN]
    have havoid (z : ℂ) (hz : z ∈ sphere (c m) (R m)) :
        z ≠ displacedRoots (a : Coeff p) n := by
      rw [hrootn]
      exact havoidFree n hnAvoid m hmK z (sphere_subset_closedBall hz)
    have hcoord := norm_sourcePsiEquationCoordinate_le_of_kernel_regularFactor
      hp hp1 n m (a : Coeff p) ψ (c m) (R m) (hR m)
        (hgeom ((a : Coeff p),ψ) hreg m).2.2.2
        havoid A B hA hkernel hregular
    calc
      ‖sourcePsiEquationCoordinate hp hp1 n m
          (a : Coeff p) ψ (c m) (R m)‖ ≤
            2*Real.pi*(R m)*(A*B) := hcoord
      _ ≤ Cdist := by dsimp [Cdist]; gcongr
      _ ≤ C := le_max_right _ _
  · have hnN : n.natAbs ≤ N := by omega
    have hns : n ∈ sN := by
      simp only [sN,Finset.mem_Icc]
      omega
    exact (hfin ((a : Coeff p),ψ) hfinite n hns m hm).trans
      (le_max_left _ _)

end NLS.ZakharovShabat
