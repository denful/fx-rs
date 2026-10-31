import FxRs.Core

/-!
Observational semantics and monad laws.

`run e s` runs `e` and answers every `pending` request with the same
context `s`. Two computations are equal when `run` agrees on all contexts.
The laws hold up to `run`, not syntactically: `adapt` always adds a
`pending` layer (`kernel/fx.rs:46`).

`run_mapM` shows that `mapM` is the bind of the state monad
`S → S × V`, Atkey's `T (S1, S2, A) = (S2 × A)^S1` with `S1 = S2`
(Atkey, "Parameterised Notions of Computation", JFP 2009).
-/

namespace FxRs.Fx

variable {S T V U W : Type}

/-- Observable meaning of a computation. -/
def run : Fx S V → S → S × V
  | immediate s v, _ => (s, v)
  | pending f, s => run (f s) s

/-- Observational equality. -/
def Equiv (e e' : Fx S V) : Prop := ∀ s, run e s = run e' s

infix:50 " ≈ " => Equiv

theorem eval_eq_run (e : Fx Unit V) : e.eval = (run e ()).2 := by
  induction e with
  | immediate _ _ => rfl
  | pending f ih => exact ih ()

/-- The one law of the kernel. All other laws follow from it. -/
theorem run_adapt (cmap : T → S) (fmap : T → S → V → Fx T U) (e : Fx S V) (t : T) :
    run (e.adapt cmap fmap) t = run (fmap t (run e (cmap t)).1 (run e (cmap t)).2) t := by
  induction e with
  | immediate _ _ => rfl
  | pending f ih => exact ih (cmap t)

theorem run_value (v : V) (s : S) : run (value v) s = (s, v) := rfl

theorem run_contraMap (get : T → S) (set : T → S → T) (e : Fx S V) (t : T) :
    run (e.contraMap get set) t = (set t (run e (get t)).1, (run e (get t)).2) := by
  simp only [contraMap, run_adapt]; rfl

/-- `mapM` is state-monad bind. -/
theorem run_mapM (f : V → Fx S U) (e : Fx S V) (s : S) :
    run (e.mapM f) s = run (f (run e s).2) (run e s).1 := by
  simp only [mapM, run_adapt, run_contraMap]; rfl

theorem mapM_left_id (v : V) (f : V → Fx S U) : (value v).mapM f ≈ f v := by
  intro s; simp only [run_mapM, run_value]

theorem mapM_right_id (e : Fx S V) : e.mapM value ≈ e := by
  intro s; simp only [run_mapM, run_value]

theorem mapM_assoc (e : Fx S V) (f : V → Fx S U) (g : U → Fx S W) :
    (e.mapM f).mapM g ≈ e.mapM fun v => (f v).mapM g := by
  intro s; simp only [run_mapM]

/-- The laws are not syntactic: right identity changes the term. -/
example : (immediate () 1 : Fx Unit Nat).mapM value ≠ immediate () 1 := by
  simp only [mapM, adapt]; nofun

end FxRs.Fx
