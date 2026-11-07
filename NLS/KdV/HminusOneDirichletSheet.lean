import NLS.KdV.HminusOneDirichletNorming
import NLS.ZakharovShabat.SobolevScalarOpenEquality

/-! The prescribed Dirichlet divisor sheet on the SAME common complex domain.
It is the actual difference of diagonal fundamental entries, independently
of every complex L2 Miura representation and constant energy shift. -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology NLS.ZakharovShabat NLS.MKdV
open scoped Classical ENNReal
namespace NLS.KdV

/-- The physical potential represented by an arbitrary shifted Miura input. -/
def shiftedMiuraSource (c : ℂ) (u : Coeff 2) : PeriodOneHminusOne :=
  periodOneMiura u-periodOneL2Inclusion (lp.single 2 0 c)

theorem continuous_shiftedMiuraSource (c : ℂ) : Continuous (shiftedMiuraSource c) :=
  continuous_periodOneMiura.sub continuous_const

/-- The open domain on which a shifted Miura source has canonical divisor data. -/
def shiftedMiuraDirichletDomain (c : ℂ) : Set (Coeff 2) :=
  shiftedMiuraSource c ⁻¹' hillHminusCanonicalDirichletDomain

theorem isOpen_shiftedMiuraDirichletDomain (c : ℂ) : IsOpen (shiftedMiuraDirichletDomain c) :=
  isOpen_hillHminusCanonicalDirichletDomain.preimage (continuous_shiftedMiuraSource c)

theorem shiftedMiuraSource_mapsTo_DirichletDomain (c : ℂ) :
    MapsTo (shiftedMiuraSource c) (shiftedMiuraDirichletDomain c) hillHminusCanonicalDirichletDomain :=
  Set.mapsTo_preimage (shiftedMiuraSource c) hillHminusCanonicalDirichletDomain

theorem mem_shiftedMiuraDirichletDomain (c : ℂ) (u : Coeff 2) :
    u ∈ shiftedMiuraDirichletDomain c ↔ shiftedMiuraSource c u ∈ hillHminusCanonicalDirichletDomain :=
  Set.mem_preimage

theorem continuousOn_DirichletNorming_shiftedMiura (n : ℕ+) (c : ℂ) :
    ContinuousOn (fun a => hillHminusDirichletNorming n (shiftedMiuraSource c a))
      (shiftedMiuraDirichletDomain c) := by
  exact ContinuousOn.comp' (f := shiftedMiuraSource c) (g := hillHminusDirichletNorming n)
    (analyticOnNhd_hillHminusDirichletNorming n).continuousOn
    (continuous_shiftedMiuraSource c).continuousOn (shiftedMiuraSource_mapsTo_DirichletDomain c)

theorem continuousOn_DirichletTerminal_shiftedMiura (n : ℕ+) (c : ℂ) :
    ContinuousOn (fun a => quasiHillL2DirichletTerminal a
      (hillHminusCanonicalDirichlet n (shiftedMiuraSource c a)+c))
      (shiftedMiuraDirichletDomain c) := by
  have henergy : ContinuousOn (fun a => hillHminusCanonicalDirichlet n (shiftedMiuraSource c a)+c)
      (shiftedMiuraDirichletDomain c) :=
    (ContinuousOn.comp' (f := shiftedMiuraSource c) (g := hillHminusCanonicalDirichlet n)
      (analyticOnNhd_hillHminusCanonicalDirichlet n).continuousOn
      (continuous_shiftedMiuraSource c).continuousOn
      (shiftedMiuraSource_mapsTo_DirichletDomain c)).add continuousOn_const
  have hc : Continuous (fun p : ℂ × Coeff 2 => quasiHillL2DirichletTerminal p.2 p.1) :=
    analyticOnNhd_quasiHillL2DirichletTerminal_joint.continuous
  have hp : ContinuousOn (fun a : Coeff 2 =>
      (hillHminusCanonicalDirichlet n (shiftedMiuraSource c a)+c,a))
      (shiftedMiuraDirichletDomain c) := henergy.prodMk continuousOn_id
  exact hc.comp_continuousOn' (f := fun a : Coeff 2 =>
    (hillHminusCanonicalDirichlet n (shiftedMiuraSource c a)+c,a)) hp

theorem hillHminusDirichletNorming_shiftedMiura_eqOn (n : ℕ+) (c : ℂ) :
    EqOn (fun a => hillHminusDirichletNorming n (shiftedMiuraSource c a))
      (fun a => quasiHillL2DirichletTerminal a (hillHminusCanonicalDirichlet n (shiftedMiuraSource c a)+c))
      (shiftedMiuraDirichletDomain c) := by
  apply eqOn_of_eqOn_scalarInclusion (f := fun a => hillHminusDirichletNorming n (shiftedMiuraSource c a))
    (g := fun a => quasiHillL2DirichletTerminal a (hillHminusCanonicalDirichlet n (shiftedMiuraSource c a)+c))
    (by simp : (2:ℝ≥0∞) ≠ ⊤)
    (isOpen_shiftedMiuraDirichletDomain c)
    (continuousOn_DirichletNorming_shiftedMiura n c) (continuousOn_DirichletTerminal_shiftedMiura n c)
  intro b hb
  have hmem := (mem_shiftedMiuraDirichletDomain c (scalarInclusion b)).mp hb
  rw [shiftedMiuraSource] at hmem ⊢
  exact hillHminusDirichletNorming_eq_shifted_sobolev n b c hmem

/-- The norming multiplier is independent of ANY valid L2 Miura lift and shift. -/
theorem hillHminusDirichletNorming_eq_shifted_miura (n : ℕ+) (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusCanonicalDirichletDomain) (u : Coeff 2) (c : ℂ)
    (hi : periodOneMiura u = q+periodOneL2Inclusion (lp.single 2 0 c)) :
    hillHminusDirichletNorming n q =
      quasiHillL2DirichletTerminal u (hillHminusCanonicalDirichlet n q+c) := by
  have hu : shiftedMiuraSource c u = q := by
    dsimp only [shiftedMiuraSource]
    rw [hi,add_sub_cancel_right]
  have hmem : shiftedMiuraSource c u ∈ hillHminusCanonicalDirichletDomain := hu.symm ▸ hq
  have humem : u ∈ shiftedMiuraDirichletDomain c := (mem_shiftedMiuraDirichletDomain c u).mpr hmem
  have h := hillHminusDirichletNorming_shiftedMiura_eqOn n c (x := u) humem
  simpa only [hu] using h

/-- The prescribed monodromy sheet, with its sign retained by the terminal multiplier. -/
def hillHminusDirichletSheet (n : ℕ+) (q : PeriodOneHminusOne) : ℂ :=
  (hillHminusDirichletNorming n q)⁻¹-hillHminusDirichletNorming n q

theorem analyticOnNhd_hillHminusDirichletSheet (n : ℕ+) :
    AnalyticOnNhd ℂ (hillHminusDirichletSheet n) hillHminusCanonicalDirichletDomain := by
  intro q hq
  exact ((analyticOnNhd_hillHminusDirichletNorming n q hq).inv
    (hillHminusDirichletNorming_ne_zero n q hq)).sub
      (analyticOnNhd_hillHminusDirichletNorming n q hq)

/-- Literal agreement with the actual diagonal difference for every Miura representation. -/
theorem hillHminusDirichletSheet_eq_shifted_miura (n : ℕ+) (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusCanonicalDirichletDomain) (u : Coeff 2) (c : ℂ)
    (hi : periodOneMiura u = q+periodOneL2Inclusion (lp.single 2 0 c)) :
    hillHminusDirichletSheet n q =
      quasiHillL2DirichletSheet u (hillHminusCanonicalDirichlet n q+c) := by
  have hz : quasiHillL2Dirichlet u (hillHminusCanonicalDirichlet n q+c) = 0 := by
    rw [← hillHminusDirichlet_eq_miura_of_shifted_image q u c _ hi]
    exact hillHminusCanonicalDirichlet_is_root n q hq
  rw [quasiHillL2DirichletSheet_of_root u _ hz,hillHminusDirichletSheet,
    hillHminusDirichletNorming_eq_shifted_miura n q hq u c hi]

/-- The trace at the divisor energy has the exact determinant-one normalization. -/
theorem hillHminusDiscriminant_at_canonicalDirichlet (n : ℕ+) (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusCanonicalDirichletDomain) :
    hillHminusDiscriminant q (hillHminusCanonicalDirichlet n q) =
      (hillHminusDirichletNorming n q)⁻¹+hillHminusDirichletNorming n q := by
  obtain ⟨B,hB⟩ := mem_iUnion.mp hq
  rw [B.canonical_dirichlet_eq n q hB,B.canonical_norming_eq n q hB,
    hillHminusDiscriminant_eq_miura_of_shifted_image q _ _ _ (B.miuraBall.actionBall.image q hB)]
  exact hillMiuraL2Discriminant_of_dirichlet_root _ _ (B.quasi_root n q hB)

/-- The chosen sheet lies above the actual discriminant square minus four. -/
theorem hillHminusDirichletSheet_sq (n : ℕ+) (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusCanonicalDirichletDomain) :
    (hillHminusDirichletSheet n q)^2 =
      (hillHminusDiscriminant q (hillHminusCanonicalDirichlet n q))^2-4 := by
  rw [hillHminusDirichletSheet,hillHminusDiscriminant_at_canonicalDirichlet n q hq]
  have hn := hillHminusDirichletNorming_ne_zero n q hq
  field_simp
  ring

end NLS.KdV
