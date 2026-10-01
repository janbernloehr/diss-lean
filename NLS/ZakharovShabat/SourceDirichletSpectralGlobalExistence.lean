import NLS.ZakharovShabat.SourceDirichletSpectralTrajectory

/-! # Global existence of actual Hilbert spectral integral curves

All local trajectories through the initial source agree on overlaps.
Their assembled curve therefore solves the actual equation throughout
its open time interval. A finite upper or lower endpoint would admit a
continuation past the supremum or infimum of that domain, contradicting
its definition. Thus the domain is all real times.
-/

noncomputable section
set_option maxHeartbeats 800000
open Set Metric Complex Filter Topology NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
local instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

private theorem exists_neg_pos_in_sourceDirichletSpectralTimeDomain
    (k : ℤ) (φ : realTypeSourceLocus 2) :
    ∃ a b : ℝ, a < 0 ∧ 0 < b ∧
      a ∈ sourceDirichletSpectralTimeDomain k φ ∧ b ∈ sourceDirichletSpectralTimeDomain k φ := by
  obtain ⟨T⟩ := nonempty_sourceDirichletSpectralTrajectory k φ
  have hL := T.initialTime_mem.1
  have hR := T.initialTime_mem.2
  refine ⟨T.lower/2,T.upper/2,by linarith,by linarith,⟨T,?_⟩,⟨T,?_⟩⟩ <;>
    constructor <;> linarith

/-- A finite supremum of the actual time domain is impossible, because
the assembled actual curve can be continued past it. -/
theorem not_bddAbove_sourceDirichletSpectralTimeDomain (k : ℤ) (φ : realTypeSourceLocus 2) :
    ¬BddAbove (sourceDirichletSpectralTimeDomain k φ) := by
  let D := sourceDirichletSpectralTimeDomain k φ
  change ¬BddAbove D
  intro hbd
  obtain ⟨a,q,ha0,hq0,ha,hq⟩ := exists_neg_pos_in_sourceDirichletSpectralTimeDomain k φ
  have hne : D.Nonempty := ⟨a,ha⟩
  let b := sSup D
  have hb0 : 0 < b := hq0.trans_le (le_csSup hbd hq)
  have hsub : Ioo a b ⊆ D := by
    intro t ht
    obtain ⟨r,hr,htr⟩ := (lt_csSup_iff hbd hne).mp ht.2
    exact (ordConnected_sourceDirichletSpectralTimeDomain k φ).out ha hr ⟨ht.1.le,htr.le⟩
  have hreal : ∀ t ∈ Ioo a b,
      IsRealType (CoeffPair.toMax 2 (sourceDirichletSpectralGlobalCurve k φ t)) :=
    fun t _ => sourceDirichletSpectralGlobalCurve_realType k φ t
  have hder : ∀ t ∈ Ioo a b, HasDerivAt (sourceDirichletSpectralGlobalCurve k φ)
      (sourceDirichletSpectralVector (by simp) (by norm_num) (by norm_num) k
        (sourceDirichletSpectralGlobalCurve k φ t)) t :=
    fun t ht => hasDerivAt_sourceDirichletSpectralGlobalCurve_of_mem k φ t (hsub ht)
  obtain ⟨ε,hε,Γ,hEq,hrealΓ,hderΓ⟩ := exists_sourceDirichletSpectral_rightContinuation
    k (sourceDirichletSpectralGlobalCurve k φ) a b (ha0.trans hb0) hreal hder
  have h0 : (0 : ℝ) ∈ Ioo a b := ⟨ha0,hb0⟩
  let T : SourceDirichletSpectralTrajectory k φ :=
    ⟨Γ,a,b+ε,⟨ha0,by linarith⟩,
      (hEq h0).trans (sourceDirichletSpectralGlobalCurve_zero k φ),hrealΓ,hderΓ⟩
  have ht : b+ε/2 ∈ D := ⟨T,⟨by dsimp [T]; linarith,by dsimp [T]; linarith⟩⟩
  have hle : b+ε/2 ≤ b := le_csSup hbd ht
  linarith

/-- A finite infimum of the actual time domain is likewise impossible. -/
theorem not_bddBelow_sourceDirichletSpectralTimeDomain (k : ℤ) (φ : realTypeSourceLocus 2) :
    ¬BddBelow (sourceDirichletSpectralTimeDomain k φ) := by
  let D := sourceDirichletSpectralTimeDomain k φ
  change ¬BddBelow D
  intro hbd
  obtain ⟨q,b,hq0,hb0,hq,hb⟩ := exists_neg_pos_in_sourceDirichletSpectralTimeDomain k φ
  have hne : D.Nonempty := ⟨b,hb⟩
  let a := sInf D
  have ha0 : a < 0 := (csInf_le hbd hq).trans_lt hq0
  have hsub : Ioo a b ⊆ D := by
    intro t ht
    obtain ⟨r,hr,hrt⟩ := (csInf_lt_iff hbd hne).mp ht.1
    exact (ordConnected_sourceDirichletSpectralTimeDomain k φ).out hr hb ⟨hrt.le,ht.2.le⟩
  have hreal : ∀ t ∈ Ioo a b,
      IsRealType (CoeffPair.toMax 2 (sourceDirichletSpectralGlobalCurve k φ t)) :=
    fun t _ => sourceDirichletSpectralGlobalCurve_realType k φ t
  have hder : ∀ t ∈ Ioo a b, HasDerivAt (sourceDirichletSpectralGlobalCurve k φ)
      (sourceDirichletSpectralVector (by simp) (by norm_num) (by norm_num) k
        (sourceDirichletSpectralGlobalCurve k φ t)) t :=
    fun t ht => hasDerivAt_sourceDirichletSpectralGlobalCurve_of_mem k φ t (hsub ht)
  obtain ⟨ε,hε,Γ,hEq,hrealΓ,hderΓ⟩ := exists_sourceDirichletSpectral_leftContinuation
    k (sourceDirichletSpectralGlobalCurve k φ) a b (ha0.trans hb0) hreal hder
  have h0 : (0 : ℝ) ∈ Ioo a b := ⟨ha0,hb0⟩
  let T : SourceDirichletSpectralTrajectory k φ :=
    ⟨Γ,a-ε,b,⟨by linarith,hb0⟩,
      (hEq h0).trans (sourceDirichletSpectralGlobalCurve_zero k φ),hrealΓ,hderΓ⟩
  have ht : a-ε/2 ∈ D := ⟨T,⟨by dsimp [T]; linarith,by dsimp [T]; linarith⟩⟩
  have hle : a ≤ a-ε/2 := csInf_le hbd ht
  linarith

/-- The actual compatible time domain is the whole real line. -/
theorem sourceDirichletSpectralTimeDomain_eq_univ (k : ℤ) (φ : realTypeSourceLocus 2) :
    sourceDirichletSpectralTimeDomain k φ = univ := by
  apply eq_univ_of_forall
  intro t
  obtain ⟨a,ha,hat⟩ := not_bddBelow_iff.mp (not_bddBelow_sourceDirichletSpectralTimeDomain k φ) t
  obtain ⟨b,hb,htb⟩ := not_bddAbove_iff.mp (not_bddAbove_sourceDirichletSpectralTimeDomain k φ) t
  exact (ordConnected_sourceDirichletSpectralTimeDomain k φ).out ha hb ⟨hat.le,htb.le⟩

/-- The assembled curve solves the actual indexed source equation at
every real time, without a finite-lifespan or extension assumption. -/
theorem hasDerivAt_sourceDirichletSpectralGlobalCurve
    (k : ℤ) (φ : realTypeSourceLocus 2) (t : ℝ) :
    HasDerivAt (sourceDirichletSpectralGlobalCurve k φ)
      (sourceDirichletSpectralVector (by simp) (by norm_num) (by norm_num) k
        (sourceDirichletSpectralGlobalCurve k φ t)) t :=
  hasDerivAt_sourceDirichletSpectralGlobalCurve_of_mem k φ t
    (by rw [sourceDirichletSpectralTimeDomain_eq_univ]; exact mem_univ t)

/-- The actual global curve conserves the original source norm and
every actual discriminant value at every real time. -/
theorem sourceDirichletSpectralGlobalCurve_conserved
    (k : ℤ) (φ : realTypeSourceLocus 2) (t : ℝ) :
    ‖sourceDirichletSpectralGlobalCurve k φ t‖ = ‖φ.val‖ ∧ ∀ w : ℂ,
      canonicalDiscriminant (by simp) (periodOnePotential (sourceDirichletSpectralGlobalCurve k φ t)) w =
        canonicalDiscriminant (by simp) (periodOnePotential φ.val) w := by
  let γ := sourceDirichletSpectralGlobalCurve k φ
  have hreal := sourceDirichletSpectralGlobalCurve_realType k φ
  have hder := hasDerivAt_sourceDirichletSpectralGlobalCurve k φ
  have hzero : γ 0 = φ.val := sourceDirichletSpectralGlobalCurve_zero k φ
  let a : ℝ := min t 0-1
  let b : ℝ := max t 0+1
  have ht : t ∈ Ioo a b := ⟨by dsimp [a]; linarith [min_le_left t 0],
    by dsimp [b]; linarith [le_max_left t 0]⟩
  have h0 : (0 : ℝ) ∈ Ioo a b := ⟨by dsimp [a]; linarith [min_le_right t 0],
    by dsimp [b]; linarith [le_max_right t 0]⟩
  constructor
  · simpa only [hzero] using
      norm_eq_on_sourceDirichletSpectral_integralCurve k γ a b
        (fun s _ => hreal s) (fun s _ => hder s) t 0 ht h0
  · intro w
    simpa only [hzero] using
      canonicalDiscriminant_eq_on_sourceDirichletSpectral_integralCurve
        (by simp) (by norm_num) (by norm_num) k γ a b (fun s _ => hder s) t 0 ht h0 w

/-- Through every real Hilbert source there is an actual real indexed
integral curve for all real times, conserving the original source norm
and every actual discriminant value, including for zero sources. -/
theorem exists_sourceDirichletSpectral_global_integralCurve
    (k : ℤ) (φ : realTypeSourceLocus 2) :
    ∃ γ : ℝ → CoeffPair 2, γ 0 = φ.val ∧
      (∀ t : ℝ, IsRealType (CoeffPair.toMax 2 (γ t))) ∧
      (∀ t : ℝ, HasDerivAt γ
        (sourceDirichletSpectralVector (by simp) (by norm_num) (by norm_num) k (γ t)) t) ∧
      ∀ t : ℝ, ‖γ t‖ = ‖φ.val‖ ∧ ∀ w : ℂ,
        canonicalDiscriminant (by simp) (periodOnePotential (γ t)) w =
          canonicalDiscriminant (by simp) (periodOnePotential φ.val) w :=
  ⟨sourceDirichletSpectralGlobalCurve k φ,sourceDirichletSpectralGlobalCurve_zero k φ,
    sourceDirichletSpectralGlobalCurve_realType k φ,hasDerivAt_sourceDirichletSpectralGlobalCurve k φ,
    sourceDirichletSpectralGlobalCurve_conserved k φ⟩

end NLS.ZakharovShabat
