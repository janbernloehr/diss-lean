import NLS.ZakharovShabat.SourcePsiGlobalTailCoordinateBound
import NLS.ZakharovShabat.SourcePsiComplexContourAnalytic
import NLS.ZakharovShabat.SourcePsiCommonJacobianCharts
import NLS.SequenceSpaces.SandwichMajorant
import Mathlib.Analysis.Complex.Schwarz

/-!
# Summable output bounds for every off-diagonal input column

The refined equation bound retains the output displacement. Along an
input-coordinate line distinct from that output, this displacement is
constant. The Schwarz lemma therefore gives one fixed `ℓᵖ` majorant
for the distant output entries, including finite head input columns.
-/

noncomputable section
open Set Filter Topology Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Every retained off-diagonal scalar column has the same summable
output majorant on valid distant free circles, uniformly as the
deleted index escapes. No cutoff on the input column is needed. -/
theorem exists_sourcePsi_escaping_allColumn_scalarTailMajorant
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (a : Coeff p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ K : ℕ, ∃ b : Coeff p,
      ∀ᶠ n : ℤ in Filter.comap Int.natAbs Filter.atTop,
        ∀ m : ℤ, K ≤ m.natAbs →
          sphere ((Real.pi : ℂ)*m) (Real.pi/8) ⊆
            sourceCanonicalRootDomain hp hp1 φ →
          ∀ k : ℤ, ∀ hkn : k ≠ n, m ≠ k →
            ‖deriv (fun t : ℂ =>
              sourcePsiDeletedEquationCoordinate hp hp1 n m
                (Coeff.deleteCoordinateTo n a +
                  Coeff.deletedSingleCLM n k hkn t) φ
                ((Real.pi : ℂ)*m) (Real.pi/8)) 0‖ ≤ ‖b m‖ := by
  obtain ⟨U,hUopen,hbase,K,C,hC,hcoord⟩ :=
    exists_local_sourcePsi_allDeleted_tailCoordinateBound hp hp1 φ hφ a
  obtain ⟨W,_,_,hrealW,hdata⟩ :=
    exists_global_sourcePsiContourIntegrand_jointAnalytic hp hp1
  let V : Set (Coeff p) := (fun v : Coeff p => (v,φ)) ⁻¹' U
  have hVopen : IsOpen V := hUopen.preimage (by fun_prop)
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hVopen a hbase
  have hrhalf : 0 < r/2 := by positivity
  let d : ℝ := 2*Real.pi*C
  let L : ℝ := 4*d/r
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  let b : Coeff p := (L : ℂ) •
    (Coeff.magnitude a +
      Coeff.magnitude (sourcePeriodicMidpointDisplacement hp hp1 φ) +
      Coeff.magnitude (sourcePeriodicGapDisplacement hp hp1 φ))
  have hnear : ∀ᶠ n : ℤ in Filter.comap Int.natAbs Filter.atTop,
      Coeff.deleteCoordinate n a ∈ ball a (r/2) :=
    (Coeff.tendsto_deleteCoordinate_at_natAbs hp a).eventually
      (isOpen_ball.mem_nhds (mem_ball_self hrhalf))
  refine ⟨K,b,?_⟩
  filter_upwards [hnear] with n hn
  intro m hm hcircle k hkn hmk
  let v (t : ℂ) : DeletedCoeff p n :=
    Coeff.deleteCoordinateTo n a + Coeff.deletedSingleCLM n k hkn t
  let f (t : ℂ) : ℂ := sourcePsiDeletedEquationCoordinate hp hp1 n m
    (v t) φ ((Real.pi : ℂ)*m) (Real.pi/8)
  let D : ℝ := ‖a m‖ +
    ‖sourcePeriodicMidpointDisplacement hp hp1 φ m‖ +
    ‖sourcePeriodicGapDisplacement hp hp1 φ m‖
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hpair (t : ℂ) (ht : t ∈ ball 0 (r/2)) :
      ((v t : Coeff p),φ) ∈ U := by
    apply hball
    apply mem_ball.mpr
    have htNorm : ‖t‖ < r/2 := by simpa using ht
    have hvdist : dist (v t : Coeff p) (Coeff.deleteCoordinate n a) = ‖t‖ := by
      rw [dist_eq_norm]
      change ‖Coeff.deleteCoordinate n a + lp.single p k t -
        Coeff.deleteCoordinate n a‖ = ‖t‖
      rw [add_sub_cancel_left,lp.norm_single
        (zero_lt_one.trans_le Fact.out)]
    calc
      dist (v t : Coeff p) a ≤
          dist (v t : Coeff p) (Coeff.deleteCoordinate n a) +
            dist (Coeff.deleteCoordinate n a) a := dist_triangle _ _ _
      _ < r := by rw [hvdist]; have h := mem_ball.mp hn; linarith
  have houtput (t : ℂ) : ‖(v t : Coeff p) m‖ ≤ ‖a m‖ := by
    by_cases hmn : m = n
    · subst m
      have hvzero : (v t : Coeff p) n = 0 := (v t).property
      rw [hvzero]
      simp
    · simp [v,Coeff.deleteCoordinateTo,
        Coeff.deleteCoordinate_apply_other n m hmn,lp.single_apply,hmk]
  have hnorm (t : ℂ) (ht : t ∈ ball 0 (r/2)) : ‖f t‖ ≤ d*D := by
    have hb := hcoord n (v t) φ (hpair t ht) m hm
    have hbaseBound :
        ‖(2*(Real.pi : ℂ))⁻¹ * f t‖ ≤ C*D :=
      hb.trans (mul_le_mul_of_nonneg_left (by
        dsimp [D]
        gcongr
        exact houtput t) hC)
    have hnonzero : 2*(Real.pi : ℂ) ≠ 0 := by
      exact mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
    calc
      ‖f t‖ = ‖(2*(Real.pi : ℂ)) * ((2*(Real.pi : ℂ))⁻¹ * f t)‖ := by
        rw [mul_inv_cancel_left₀ hnonzero]
      _ = (2*Real.pi)*‖(2*(Real.pi : ℂ))⁻¹ * f t‖ := by
        rw [norm_mul]
        simp [abs_of_pos Real.pi_pos]
      _ ≤ (2*Real.pi)*(C*D) := by gcongr
      _ = d*D := by dsimp [d]; ring
  have hdiff : DifferentiableOn ℂ f (ball 0 (r/2)) := by
    intro t ht
    have hbaseDiff :=
      differentiableAt_sourcePsiEquationCoordinate_of_contour_domain
        hp hp1 n m (v t : Coeff p) φ ((Real.pi : ℂ)*m) (Real.pi/8)
        (by positivity) W (hrealW hφ) (hdata n).1 (hdata n).2 hcircle
    have hlineDiff : Differentiable ℂ
        (fun t : ℂ => ((v t : Coeff p),φ)) := by
      have hv : Differentiable ℂ (fun t : ℂ => (v t : Coeff p)) := by
        change Differentiable ℂ (fun t : ℂ =>
          Coeff.deleteCoordinate n a +
            (lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) p k) t)
        exact (lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) p k).differentiable.const_add
          (Coeff.deleteCoordinate n a)
      exact hv.prodMk (differentiable_const φ)
    exact (hbaseDiff.comp t (hlineDiff t)).differentiableWithinAt
  have hmaps : MapsTo f (ball 0 (r/2)) (closedBall (f 0) (2*d*D)) := by
    intro t ht
    rw [mem_closedBall,dist_eq_norm]
    exact (norm_sub_le _ _).trans (by
      have h := add_le_add (hnorm t ht) (hnorm 0 (mem_ball_self hrhalf))
      nlinarith)
  have hderiv := Complex.norm_deriv_le_div_of_mapsTo_ball hdiff hmaps hrhalf
  have hb : ‖b m‖ = L*D := by
    simp only [b,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,norm_mul,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hL,
      lp.coeFn_add,Pi.add_apply,Coeff.magnitude_apply,← Complex.ofReal_add]
    change L*|D| = L*D
    rw [abs_of_nonneg hD]
  change ‖deriv f 0‖ ≤ ‖b m‖
  rw [hb]
  convert hderiv using 1
  dsimp [L]
  field_simp
  ring

/-- On any common valid contour family with the retained-entry
identities, distant output entries of every off-diagonal column share
one `ℓᵖ` majorant. The deleted row and column also satisfy the bound. -/
theorem sourcePsiFullRootJacobian_allColumn_tailMajorant
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (a : Coeff p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (c : ℤ → ℂ) (R : ℤ → ℝ)
    (hcircle : ∀ m : ℤ,
      sphere (c m) (R m) ⊆ sourceCanonicalRootDomain hp hp1 φ)
    (Kfree : ℕ)
    (hfree : ∀ m : ℤ, Kfree < m.natAbs →
      c m = (Real.pi : ℂ)*m ∧ R m = Real.pi/8)
    (hmatrix : ∀ᶠ n : ℤ in Filter.comap Int.natAbs Filter.atTop,
      ∀ m k : ℤ, ∀ _hmn : m ≠ n, ∀ hkn : k ≠ n,
        (sourcePsiFullRootJacobian hp hp1 n c R
          (Coeff.deleteCoordinateTo n a) φ (lp.single p k 1)) m =
          deriv (fun t : ℂ =>
            sourcePsiDeletedEquationCoordinate hp hp1 n m
              (Coeff.deleteCoordinateTo n a +
                Coeff.deletedSingleCLM n k hkn t) φ (c m) (R m)) 0) :
    ∃ K : ℕ, ∃ b : Coeff p,
      ∀ᶠ n : ℤ in Filter.comap Int.natAbs Filter.atTop,
        ∀ m k : ℤ, K ≤ m.natAbs → m ≠ k →
          ‖(sourcePsiFullRootJacobian hp hp1 n c R
            (Coeff.deleteCoordinateTo n a) φ (lp.single p k 1)) m‖ ≤ ‖b m‖ := by
  obtain ⟨Kscalar,b,hscalar⟩ :=
    exists_sourcePsi_escaping_allColumn_scalarTailMajorant hp hp1 a φ hφ
  refine ⟨max Kscalar (Kfree+1),b,?_⟩
  filter_upwards [hmatrix,hscalar] with n hn hs
  intro m k hm hmk
  by_cases hmn : m = n
  · subst m
    rw [sourcePsiFullRootJacobian_entry_deleted_row hp hp1 n k hmk.symm]
    simp
  by_cases hkn : k = n
  · subst k
    rw [sourcePsiFullRootJacobian_entry_deleted_column hp hp1 n m hmn]
    simp
  have hmScalar : Kscalar ≤ m.natAbs := by omega
  have hmFree : Kfree < m.natAbs := by omega
  have hc := hfree m hmFree
  have hcircleFree : sphere ((Real.pi : ℂ)*m) (Real.pi/8) ⊆
      sourceCanonicalRootDomain hp hp1 φ := by
    simpa only [hc.1,hc.2] using hcircle m
  rw [hn m k hmn hkn,hc.1,hc.2]
  exact hs m hmScalar hcircleFree k hkn hmk

end NLS.ZakharovShabat
