module

public import PakStokes.CubeNome
public import PakStokes.PolynomialFlow
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import all PakStokes.CubeNome
import all PakStokes.RegularCube

/-! The physical coordinate chart and analytic continuation of a local
autonomous equation along the connected positive ray. -/
public section
namespace CubicTheta.Nome
open Filter Set Complex MvPolynomial
open scoped Topology
noncomputable section

def qRay (p : ℝ) : ℂ := (Real.exp (-(1/p^2)):ℝ)
def recip (p : ℝ) : ℂ := (p:ℂ)⁻¹
def pole (p : ℝ) : ℂ := ((p^(2/3:ℝ):ℝ):ℂ)
def speed (p : ℝ) := 2*(recip p)^3*qRay p
def source (i : ℕ) (p : ℝ) := analyticCoordinates (qRay p) i

theorem qRay_disk {p : ℝ} (hp : 0<p) : ‖qRay p‖ < 1 := by
  rw [qRay,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),Real.exp_lt_one_iff]; exact neg_lt_zero.mpr (by positivity)

theorem qRay_deriv {p : ℝ} (hp : 0<p) : HasDerivAt qRay (speed p) p := by
  have h := (((hasDerivAt_const p (1:ℝ)).div (hasDerivAt_pow 2 p) (by positivity)).neg.exp).ofReal_comp
  convert h using 1
  · rfl
  · simp [speed,recip,qRay,Pi.div_apply]; field_simp [hp.ne']

theorem qRay_analytic {p : ℝ} (hp : 0<p) : AnalyticAt ℝ qRay p := by
  apply (Complex.ofRealCLM.analyticAt _).comp
  exact ((analyticAt_const.div (analyticAt_id.pow 2) (pow_ne_zero _ hp.ne')).neg).rexp

theorem recip_deriv {p : ℝ} (hp : 0<p) : HasDerivAt recip (-recip p^2) p := by
  simpa [recip,div_eq_mul_inv] using! Complex.ofRealCLM.hasDerivAt.inv (show (p:ℂ)≠0 by exact_mod_cast hp.ne')

theorem pole_deriv {p : ℝ} (hp : 0<p) : HasDerivAt pole ((2/3:ℂ)*recip p*pole p) p := by
  have h := (Real.hasDerivAt_rpow_const (x := p) (p := 2/3) (Or.inl hp.ne')).ofReal_comp
  convert h using 1
  · rfl
  · rw [Real.rpow_sub hp,Real.rpow_one]; unfold pole recip; push_cast; ring

theorem pole_analytic {p : ℝ} (hp : 0<p) : AnalyticAt ℝ pole p := by
  have he : pole =ᶠ[𝓝 p] fun x : ℝ ↦ (Real.exp (Real.log x*(2/3:ℝ)):ℂ) :=
    (lt_mem_nhds hp).mono fun x hx ↦ by simp [pole,Real.rpow_def_of_pos hx]
  apply AnalyticAt.congr _ he.symm
  exact (Complex.ofRealCLM.analyticAt _).comp ((analyticAt_log hp).mul analyticAt_const).rexp

theorem source_deriv {p : ℝ} (hp : 0<p) (j : ℕ) :
    HasDerivAt (source (j+1)) (speed p*source (j+2) p) p := by
  simpa [source,analyticCoordinates,Function.comp_def,mul_comm] using!
    ((jet_deriv j (qRay_disk hp)).scomp p (qRay_deriv hp))

theorem source_analytic {p : ℝ} (hp : 0<p) (j : ℕ) : AnalyticAt ℝ (source j) p := by
  cases j with
  | zero => exact qRay_analytic hp
  | succ j =>
    exact (((jet_analytic j) _ (by simpa using qRay_disk hp)).restrictScalars (𝕜 := ℝ)).comp (qRay_analytic hp)

theorem regular_at {p : ℝ} (hp : 0<p) :
    Physical.regularCube p = source 1 p - (1/2 + (Real.Gamma (4/3):ℂ)*pole p) := by
  change _ = value H (qRay p) - _
  rw [physical_series]
  unfold Physical.regularCube
  congr 1
  · apply tsum_congr; intro n
    simp only [qRay,← Complex.ofReal_pow,← Real.exp_nat_mul,Nat.cast_pow]
    congr 2; ring
  · have h : (1/p^2)^(-(1:ℝ)/3) = p^(2/3:ℝ) := by
      rw [one_div,Real.inv_rpow (sq_nonneg _),← Real.rpow_natCast_mul hp.le]
      rw [← Real.rpow_neg hp.le]; congr 1; norm_num
    rw [h]; simp [pole,mul_comm]

theorem regular_analytic {p : ℝ} (hp : 0<p) : AnalyticAt ℝ Physical.regularCube p := by
  apply ((source_analytic hp 1).sub (analyticAt_const.add (analyticAt_const.mul (pole_analytic hp)))).congr
  exact (lt_mem_nhds hp).mono fun _ h ↦ (regular_at h).symm

theorem local_to_tail {J : ℕ} (P : MvPolynomial (Fin J) ℂ) {x : ℝ} (hx : 0<x)
    (h : ∀ᶠ p in 𝓝 x, eval (fun i : Fin J ↦ iteratedDeriv i.val Physical.regularCube p) P=0) :
    ∀ᶠ p : ℝ in atTop, eval (fun i : Fin J ↦ iteratedDeriv i.val Physical.regularCube p) P=0 := by
  have an (p : ℝ) (hp : 0<p) (k : ℕ) : AnalyticAt ℝ (iteratedDeriv k Physical.regularCube) p := by
    induction k with
    | zero => simpa using regular_analytic hp
    | succ k ih => rw [iteratedDeriv_succ]; exact ih.deriv
  have all : AnalyticOnNhd ℝ (fun p ↦ eval (fun i : Fin J ↦ iteratedDeriv i.val Physical.regularCube p) P) (Ioi 0) := by
    clear h; intro p hp; induction P using MvPolynomial.induction_on with
    | C => simpa using analyticAt_const
    | add a b ha hb => simpa only [map_add] using! ha.add hb
    | mul_X a i ha => simpa only [map_mul,eval_X] using! ha.mul (an p hp i.val)
  exact (eventually_gt_atTop (0:ℝ)).mono fun p hp ↦
    all.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_Ioi _).isPreconnected hx h hp
end
end CubicTheta.Nome
