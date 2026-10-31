import FxRs.Core

/-!
Rust tests mirrored as definitional equalities. Each example names its
Rust test. A wrong model fails `rfl`.
-/

namespace FxRs.Examples
open Fx

/-- `Ctx { a: i32, b: String }` in `core/tests/provide_test.rs`. -/
abbrev Ctx := Int × String

def setA (c : Ctx) (a : Int) : Ctx := (a, c.2)
def setB (c : Ctx) (b : String) : Ctx := (c.1, b)

/-- `provide_has_sets_field`. -/
example :
    ((pending fun c : Ctx => value c.1 : Fx Ctx Int).updateContext setA 42
      |>.provide (0, "init")).eval = 42 := rfl

/-- `provide_has_sets_string_field`. -/
example :
    ((pending fun c : Ctx => value c.2 : Fx Ctx String).updateContext setB "hello"
      |>.provide (0, "init")).eval = "hello" := rfl

/-- `update_context_replaces_part_of_context`. -/
example :
    let a : Fx Ctx Int := (func fun u : Int => u * 2).lift Prod.fst setA
    ((a.mapM fun n => (a.updateContext setA 10).map fun m => (n, m))
      |>.provide (7, "init")).eval = (14, 20) := rfl

/-- Negative control: the same program does not give a wrong value. -/
example :
    let a : Fx Ctx Int := (func fun u : Int => u * 2).lift Prod.fst setA
    ((a.mapM fun n => (a.updateContext setA 10).map fun m => (n, m))
      |>.provide (7, "init")).eval ≠ (14, 14) := by decide

/-- `map_m` threads the context: `State::set` then a read sees the new value. -/
example :
    ((immediate 5 () : Fx Int Unit).mapM (fun _ => get id) |>.provide 0).eval = 5 := rfl

end FxRs.Examples
