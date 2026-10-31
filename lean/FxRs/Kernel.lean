/-!
Model of the fx-rs kernel: `crates/fx/src/kernel/fx.rs`.

`Clone` bounds and lifetimes are not modelled. A Rust `Ability<S, S, V>`
is a function `S → Fx S V` here.
-/

namespace FxRs

/-- `Eff` in `kernel/fx.rs:7-10`. -/
inductive Fx (S V : Type) where
  | immediate : S → V → Fx S V
  | pending : (S → Fx S V) → Fx S V

namespace Fx

variable {S T V U : Type}

/-- `Fx::adapt` in `kernel/fx.rs:36-51`. The result is always `pending`,
as in Rust. -/
def adapt (cmap : T → S) (fmap : T → S → V → Fx T U) : Fx S V → Fx T U
  | immediate s v => pending fun t => fmap t s v
  | pending f => pending fun t => adapt cmap fmap (f (cmap t))

/-- `Fx::eval` in `kernel/fx.rs:12-22`. Only a computation over the unit
context can run. -/
def eval : Fx Unit V → V
  | immediate _ v => v
  | pending f => eval (f ())

end Fx

end FxRs
