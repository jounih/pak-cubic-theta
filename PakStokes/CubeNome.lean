module

public import PakStokes.RegularCube
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Algebra.MvPolynomial.Eval
import all PakStokes.RegularCube

/-! Evaluation in the original nome. Formal polynomial identities in the
cube power series and its ordinary formal derivatives hold on the open
unit disk, with the same derivatives as the analytic function. -/
public section
namespace CubicTheta.Nome
open Set Filter Complex Metric PowerSeries
open scoped Topology
noncomputable section

def H : PowerSeries ℂ := by classical exact PowerSeries.mk fun k ↦ if ∃ n : ℕ, n^3=k then 1 else 0
def jet (j : ℕ) := (PowerSeries.derivative (R := ℂ))^[j] H
def term (S : PowerSeries ℂ) (q : ℂ) (n : ℕ) := PowerSeries.coeff n S * q^n
def value (S : PowerSeries ℂ) (q : ℂ) := ∑' n, term S q n
def AbsAt (S : PowerSeries ℂ) (q : ℂ) := Summable (fun n ↦ ‖term S q n‖)

private theorem coeff_bound (j n : ℕ) : ‖PowerSeries.coeff n (jet j)‖ ≤ j.factorial*(n+1:ℝ)^j := by
  rw [jet,PowerSeries.coeff_iterate_derivative,H,PowerSeries.coeff_mk]
  split_ifs
  · simpa using (show (↑((n+1).ascFactorial j):ℝ) ≤ j.factorial*(n+1:ℝ)^j by
      exact_mod_cast Nat.ascFactorial_le_factorial_mul_pow (n+1) j)
  · simp; positivity

private theorem shifted_geom (j : ℕ) {r : ℝ} (hr : 0 < r) (h1 : r < 1) :
    Summable (fun n : ℕ ↦ (n+1:ℝ)^j*r^n) := by
  have hs := (summable_pow_mul_geometric_of_norm_lt_one j (show ‖r‖<1 by simpa [abs_of_pos hr] using h1))
  have h := (hs.comp_injective (show Function.Injective (fun n : ℕ ↦ n+1) by intro i k hh; exact Nat.add_right_cancel hh)).mul_right r⁻¹
  simpa [Function.comp_def,pow_succ,mul_assoc,hr.ne'] using h

private theorem bound_on (j : ℕ) {q : ℂ} {r : ℝ} (h : ‖q‖ ≤ r) (n : ℕ) :
    ‖term (jet j) q n‖ ≤ j.factorial*((n+1:ℝ)^j*r^n) := by
  rw [term,norm_mul,norm_pow,← mul_assoc]
  exact mul_le_mul (coeff_bound j n) (pow_le_pow_left₀ (norm_nonneg _) h _) (by positivity) (by positivity)

theorem jet_abs (j : ℕ) {q : ℂ} (hq : ‖q‖ < 1) : AbsAt (jet j) q := by
  obtain ⟨r,hr,h1⟩ := exists_between hq
  exact ((shifted_geom j ((norm_nonneg _).trans_lt hr) h1).mul_left _).of_nonneg_of_le
    (fun _ ↦ norm_nonneg _) (bound_on j hr.le)

theorem jet_deriv (j : ℕ) {q : ℂ} (hq : ‖q‖ < 1) :
    HasDerivAt (value (jet j)) (value (jet (j+1)) q) q := by
  obtain ⟨r,hr,h1⟩ := exists_between hq
  have rp := (norm_nonneg _).trans_lt hr
  let f (n : ℕ) (z : ℂ) := term (jet j) z (n+1)
  let g (n : ℕ) (z : ℂ) := term (jet (j+1)) z n
  have hd (n : ℕ) (z : ℂ) : HasDerivAt (f n) (g n z) z := by
    have he : PowerSeries.coeff n (jet (j+1)) = PowerSeries.coeff (n+1) (jet j) * (n+1) := by
      rw [jet,Function.iterate_succ_apply',PowerSeries.coeff_derivative]; rfl
    simpa [f,g,term,he,mul_assoc] using ((hasDerivAt_pow (n+1) z).const_mul (PowerSeries.coeff (n+1) (jet j)))
  have hs := hasDerivAt_tsum_of_isPreconnected ((shifted_geom (j+1) rp h1).mul_left (↑(j+1).factorial))
    (t := ball (0:ℂ) r) isOpen_ball ((convex_ball (0:ℂ) _).isPreconnected)
    (fun n z _ ↦ hd n z) (fun n z hz ↦ bound_on _ (by simpa using (mem_ball.mp hz).le) n)
    (y₀ := q) (by simpa using hr)
    ((jet_abs j hq).of_norm.comp_injective (show Function.Injective (fun n : ℕ ↦ n+1) by intro i k hh; exact Nat.add_right_cancel hh)) (by simpa using hr)
  have near : value (jet j) =ᶠ[𝓝 q] fun z ↦ PowerSeries.coeff 0 (jet j) + ∑' n, f n z := by
    filter_upwards [isOpen_ball.mem_nhds (show q ∈ ball (0:ℂ) 1 by simpa using hq)] with z hz
    have h := (jet_abs j (by simpa using hz : ‖z‖<1)).of_norm.sum_add_tsum_nat_add 1
    simpa [value,f,term] using h.symm
  exact (hs.const_add _).congr_of_eventuallyEq near

theorem jet_analytic (j : ℕ) : AnalyticOnNhd ℂ (value (jet j)) (ball 0 1) := by
  apply DifferentiableOn.analyticOnNhd _ isOpen_ball
  intro q hq; exact (jet_deriv j (by simpa using hq)).differentiableAt.differentiableWithinAt

theorem physical_series (q : ℂ) : value H q = ∑' n : ℕ, q^(n^3) := by
  classical
  let f (n : ℕ) := n^3
  have inj : Function.Injective f := Nat.pow_left_injective (by decide : 3≠0)
  have eqn := inj.tsum_eq (f := term H q) (fun k hk ↦ by
    by_contra no
    change ¬ ∃ n : ℕ, n^3=k at no
    exact hk (by simp [term,H,no]))
  simpa [value,term,H,f] using eqn.symm

private theorem conv_term (S T : PowerSeries ℂ) (q : ℂ) (n : ℕ) :
    term (S*T) q n = ∑ kl ∈ Finset.antidiagonal n, term S q kl.1 * term T q kl.2 := by
  rw [term,PowerSeries.coeff_mul,Finset.sum_mul]
  apply Finset.sum_congr rfl; intro kl h
  rw [← Finset.mem_antidiagonal.mp h,pow_add]; unfold term; ring

private theorem eval_add {S T : PowerSeries ℂ} {q : ℂ} (h : AbsAt S q) (k : AbsAt T q) :
    AbsAt (S+T) q ∧ value (S+T) q = value S q+value T q := by
  have he : term (S+T) q = fun n ↦ term S q n+term T q n := by funext n; simp [term,add_mul]
  exact ⟨by unfold AbsAt; rw [he]; exact (h.add k).of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun _ ↦ norm_add_le ..),
    by simp only [value,he,h.of_norm.tsum_add k.of_norm]⟩

private theorem eval_mul {S T : PowerSeries ℂ} {q : ℂ} (h : AbsAt S q) (k : AbsAt T q) :
    AbsAt (S*T) q ∧ value (S*T) q = value S q*value T q := by
  constructor
  · simpa only [AbsAt,conv_term] using summable_norm_sum_mul_antidiagonal_of_summable_norm h k
  · simpa only [value,conv_term] using (tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm h k).symm

private theorem eval_const (c q : ℂ) : AbsAt (PowerSeries.C c) q ∧ value (PowerSeries.C c) q = c := by
  classical
  have he : term (PowerSeries.C c) q = Pi.single 0 c := by
    funext n; by_cases hn : n=0 <;> simp [term,PowerSeries.coeff_C,hn]
  simp [AbsAt,value,he,Pi.single_apply,apply_ite (fun z : ℂ ↦ ‖z‖)]
  exact summable_of_ne_finset_zero (s := {0}) (by simp_all)

theorem polynomial_value {ι : Type*} (P : MvPolynomial ι ℂ) {S : ι → PowerSeries ℂ}
    {q : ℂ} (hs : ∀ i, AbsAt (S i) q) :
    AbsAt (MvPolynomial.aeval S P) q ∧ value (MvPolynomial.aeval S P) q =
      MvPolynomial.eval (fun i ↦ value (S i) q) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simpa [PowerSeries.algebraMap_apply] using eval_const c q
  | add p t hp ht =>
    simpa [hp.2,ht.2] using eval_add hp.1 ht.1
  | mul_X p i hp => simpa [hp.2] using eval_mul hp.1 (hs i)

theorem nome_abs (q : ℂ) : AbsAt PowerSeries.X q ∧ value PowerSeries.X q = q := by
  classical
  have he : term PowerSeries.X q = Pi.single 1 q := by
    funext n; by_cases hn : n=1 <;> simp [term,PowerSeries.coeff_X,hn]
  simp [AbsAt,value,he,Pi.single_apply,apply_ite (fun z : ℂ ↦ ‖z‖)]
  exact summable_of_ne_finset_zero (s := {1}) (by simp_all)

/-- The original formal series with ordinary derivatives and the independent
variable itself. Clearing denominators permits polynomial coefficients in q. -/
def coordinates : ℕ → PowerSeries ℂ
  | 0 => PowerSeries.X
  | j+1 => jet j

def analyticCoordinates (q : ℂ) : ℕ → ℂ
  | 0 => q
  | j+1 => value (jet j) q

theorem formal_identity_on_disk (P : MvPolynomial ℕ ℂ)
    (zero : MvPolynomial.aeval coordinates P = 0) {q : ℂ} (hq : ‖q‖ < 1) :
    MvPolynomial.eval (analyticCoordinates q) P = 0 := by
  have ha (j) : AbsAt (coordinates j) q := by cases j with
    | zero => exact (nome_abs q).1
    | succ j => exact jet_abs j hq
  have he : (fun i ↦ value (coordinates i) q) = analyticCoordinates q := by
    funext i; cases i with
    | zero => exact (nome_abs q).2
    | succ j => rfl
  have hh := (polynomial_value P ha).2; rw [zero,he] at hh; simpa [value,term] using hh.symm

end
end CubicTheta.Nome
