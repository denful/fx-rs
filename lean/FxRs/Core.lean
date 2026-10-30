import FxRs.Kernel

/-!
Core operations, all derived from `adapt`. Sources:
`crates/fx/src/core/fx.rs`, `core/state.rs`, `core/provide.rs`.

`Has<T>` and `Put<T, S>` are passed as explicit `get` and `put` functions.
-/

namespace FxRs.Fx

variable {S T V U A : Type}

/-- `Fx::pure` (`core/fx.rs:8`). -/
def pure (v : V) : Fx Unit V := immediate () v

/-- `Fx::value` (`core/fx.rs:14`). -/
def value (v : V) : Fx S V := pending fun s => immediate s v

/-- `Fx::contra_map` (`core/fx.rs`). -/
def contraMap (get : T → S) (set : T → S → T) (e : Fx S V) : Fx T V :=
  e.adapt get fun t s v => immediate (set t s) v

/-- `Fx::map_m` (`core/fx.rs:25-31`). The next step reads the final
context `s` of this step. -/
def mapM (f : V → Fx S U) (e : Fx S V) : Fx S U :=
  e.adapt id fun _ s v => (f v).contraMap (fun _ => s) fun _ s => s

/-- `Fx::map` (`core/fx.rs`). -/
def map (f : V → U) (e : Fx S V) : Fx S U :=
  e.mapM fun v => value (f v)

/-- `State::get` (`core/state.rs:10-16`). -/
def get (has : S → A) : Fx S A := pending fun s => immediate s (has s)

/-- `Fx::func` (`core/fx.rs:18-23`). -/
def func (f : S → V) : Fx S V := (get id).map f

/-- `Fx::lift` (`core/fx.rs`). -/
def lift (has : T → S) (put : T → S → T) (e : Fx S V) : Fx T V :=
  e.contraMap has put

/-- `Fx::provide` (`core/provide.rs:5-7`). -/
def provide (s : S) (e : Fx S V) : Fx T V :=
  e.contraMap (fun _ => s) fun t _ => t

/-- `Fx::update_context` (`core/provide.rs:20-26`). -/
def updateContext (put : S → A → S) (a : A) (e : Fx S V) : Fx S V :=
  e.contraMap (fun p => put p a) fun _ p => p

end FxRs.Fx
