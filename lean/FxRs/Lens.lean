import FxRs.Laws

/-!
Lens laws and the scope of `update_context`.

`Lens` models `core/lens.rs:13` (`get`, `set`). `zoomOut` models
`Lens::zoom_out` (`core/lens.rs:34-39`).
-/

namespace FxRs

structure Lens (O I : Type) where
  get : O → I
  set : O → I → O

/-- The three very well-behaved lens laws. -/
structure Lens.Lawful {O I : Type} (l : Lens O I) : Prop where
  get_set : ∀ o, l.set o (l.get o) = o
  set_get : ∀ o i, l.get (l.set o i) = i
  set_set : ∀ o i j, l.set (l.set o i) j = l.set o j

namespace Fx

variable {O I V A : Type}

def zoomOut (l : Lens O I) (e : Fx I V) : Fx O V := e.contraMap l.get l.set

/-- A computation that does not change its context. -/
def Pure (e : Fx I V) : Prop := ∀ s, (run e s).1 = s

/-- Framing: a pure inner computation leaves the outer context unchanged. -/
theorem zoomOut_pure (l : Lens O I) (hl : l.Lawful) (e : Fx I V) (he : e.Pure) :
    (zoomOut l e).Pure := by
  intro o; simp only [zoomOut, run_contraMap]; rw [he (l.get o), hl.get_set]

/-- The inner write is the outer field after the step. -/
theorem zoomOut_get (l : Lens O I) (hl : l.Lawful) (e : Fx I V) (o : O) :
    l.get (run (zoomOut l e) o).1 = (run e (l.get o)).1 := by
  simp only [zoomOut, run_contraMap, hl.set_get]

/-- `update_context` (`core/provide.rs:24`) is `put`, not `local`: the new
value stays in the context after the step. -/
theorem run_updateContext (put : I → A → I) (a : A) (e : Fx I V) (s : I) :
    run (e.updateContext put a) s = run e (put s a) := by
  simp only [updateContext, run_contraMap]

/-- Reader-`local` over a lens: replace the field for `e` only, then put the
original field back. -/
def «local» (l : Lens O I) (i : I) (e : Fx O V) : Fx O V :=
  e.contraMap (fun o => l.set o i) fun o o' => l.set o' (l.get o)

theorem local_restores (l : Lens O I) (hl : l.Lawful) (i : I) (e : Fx O V) (o : O) :
    l.get (run (e.«local» l i) o).1 = l.get o := by
  simp only [«local», run_contraMap, hl.set_get]

end Fx

namespace LensExamples
open Fx

abbrev Ctx := Int × String

def fieldA : Lens Ctx Int := ⟨Prod.fst, fun c a => (a, c.2)⟩

theorem fieldA_lawful : fieldA.Lawful :=
  ⟨fun _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl⟩

/-- Reads field `a`, doubled (`provide_test.rs`, `update_context_replaces_part_of_context`). -/
def readA : Fx Ctx Int := (func fun u : Int => u * 2).lift fieldA.get fieldA.set

/-- Witness for #3: after `update_context`, the next step still sees 10. -/
example :
    ((readA.updateContext fieldA.set 10).mapM (fun _ => readA)
      |>.provide (7, "x")).eval = 20 := rfl

/-- With `local`, the next step sees the original 7 again. -/
example :
    ((readA.«local» fieldA 10).mapM (fun _ => readA)
      |>.provide (7, "x")).eval = 14 := rfl

end LensExamples

end FxRs
