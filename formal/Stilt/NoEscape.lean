import Stilt.Declarations

/-!
# The no-escape rule

A non-escaping parameter passes its argument's effects through to the caller,
which can only be sound while the argument runs during the call. So each
occurrence of a non-escaping parameter in its function's body, and each closure
literal that names one, must be the callee of a call, or an argument given to a
non-escaping parameter of the function that a call names (effects.no-escape).
Anything else is E0508.

The rule is one syntactic pass over a body, like the law of exclusivity, and
sees variables, never types. A binder that reuses a parameter's name hides the
parameter in its scope, as typing's contexts do (expressions.shadowing).
-/

namespace Stilt

/-- The names of a function's non-escaping parameters (effects.non-escaping-parameters). -/
def FnDecl.nonEscaping (d : FnDecl) : List Name :=
  d.params.filterMap fun p => p.implicit.map fun _ => p.name

/-- For each parameter of the function that a callee names, whether it is
non-escaping. A callee that isn't a declared function's name has none: an
argument given to a function value's parameter escapes (effects.no-escape). -/
def Decls.passing (D : Decls) : Expr → List Bool
  | .fnRef f _ _ => (D.fn? f).elim [] fun d => d.params.map (·.implicit.isSome)
  | _ => []

mutual

/-- Whether `e` names one of the variables `N` where they are free in it. -/
def Expr.names (N : List Name) : Expr → Bool
  | .var x | .move x => N.contains x
  | .int _ | .bool _ | .unit | .break | .continue | .fnRef _ _ _ | .method _ _ _ => false
  | .record _ _ fields => fieldsNames N fields
  | .variant _ _ _ es | .list _ es | .op _ es | .view es => exprsNames N es
  | .field e _ | .raise e | .perform _ e | .try e | .loop e | .return e => e.names N
  | .index a b | .seq a b | .withH _ _ a b | .while a b => a.names N || b.names N
  | .closure ps _ _ body => body.names (N.removeAll (ps.map Param.name))
  | .call f args _ => f.names N || argsNames N args
  | .letIn x _ init body | .varIn x _ init body =>
    init.names N || body.names (N.removeAll [x])
  | .held ns hs body => exprsNames N hs || body.names (N.removeAll (ns.map (·.1)))
  | .assign ⟨x, path⟩ v => N.contains x || pathNames N path || v.names N
  | .if c _ a b => c.names N || a.names N || b.names N
  | .match e _ arms => e.names N || armsNames N arms
  | .for x _ e body => e.names N || body.names (N.removeAll [x])
  | .tryCatch e _ x h _ => e.names N || h.names (N.removeAll [x])

/-- Whether an expression of a list names one of `N`. -/
def exprsNames (N : List Name) : List Expr → Bool
  | [] => false
  | e :: es => e.names N || exprsNames N es

/-- Whether a field of a record literal names one of `N`. -/
def fieldsNames (N : List Name) : List (Name × Expr) → Bool
  | [] => false
  | (_, e) :: fields => e.names N || fieldsNames N fields

/-- Whether an argument names one of `N`. -/
def argsNames (N : List Name) : List Arg → Bool
  | [] => false
  | .value e :: args => e.names N || argsNames N args
  | .inout ⟨x, path⟩ :: args => N.contains x || pathNames N path || argsNames N args

/-- Whether an index of a place names one of `N`. -/
def pathNames (N : List Name) : List Projection → Bool
  | [] => false
  | .field _ :: path => pathNames N path
  | .index i :: path => i.names N || pathNames N path

/-- Whether an arm names one of `N` outside its binders. -/
def armsNames (N : List Name) : List Arm → Bool
  | [] => false
  | ⟨_, binders, body⟩ :: arms => body.names (N.removeAll binders) || armsNames N arms

end

mutual

/-- No non-escaping parameter among `N` escapes from `e`. `allowed` says that
`e` is a callee, or an argument given to a non-escaping parameter of the
function a call names: there `e` may be one of `N`, or a closure literal that
names them (effects.no-escape). Elsewhere neither may occur. -/
def Expr.noEscape (D : Decls) (N : List Name) (allowed : Bool) : Expr → Bool
  | .var x | .move x => allowed || !N.contains x
  | .int _ | .bool _ | .unit | .break | .continue | .fnRef _ _ _ | .method _ _ _ => true
  | .record _ _ fields => fieldsNoEscape D N fields
  | .variant _ _ _ es | .list _ es | .op _ es | .view es => exprsNoEscape D N es
  | .field e _ | .raise e | .perform _ e | .try e | .loop e | .return e => e.noEscape D N false
  | .index a b | .seq a b | .withH _ _ a b | .while a b => a.noEscape D N false && b.noEscape D N false
  | .closure ps _ _ body =>
    let N' := N.removeAll (ps.map Param.name)
    (allowed || !body.names N') && body.noEscape D N' false
  | .call f args _ => f.noEscape D N true && argsNoEscape D N (D.passing f) args
  | .letIn x _ init body | .varIn x _ init body =>
    init.noEscape D N false && body.noEscape D (N.removeAll [x]) false
  | .held ns hs body => exprsNoEscape D N hs && body.noEscape D (N.removeAll (ns.map (·.1))) false
  | .assign ⟨x, path⟩ v => !N.contains x && pathNoEscape D N path && v.noEscape D N false
  | .if c _ a b => c.noEscape D N false && a.noEscape D N false && b.noEscape D N false
  | .match e _ arms => e.noEscape D N false && armsNoEscape D N arms
  | .for x _ e body => e.noEscape D N false && body.noEscape D (N.removeAll [x]) false
  | .tryCatch e _ x h _ => e.noEscape D N false && h.noEscape D (N.removeAll [x]) false

/-- No parameter of `N` escapes from the expressions of a list. -/
def exprsNoEscape (D : Decls) (N : List Name) : List Expr → Bool
  | [] => true
  | e :: es => e.noEscape D N false && exprsNoEscape D N es

/-- No parameter of `N` escapes from the fields of a record literal. -/
def fieldsNoEscape (D : Decls) (N : List Name) : List (Name × Expr) → Bool
  | [] => true
  | (_, e) :: fields => e.noEscape D N false && fieldsNoEscape D N fields

/-- No parameter of `N` escapes from the arguments of a call, given for each
of the callee's parameters, in order, whether it is non-escaping. -/
def argsNoEscape (D : Decls) (N : List Name) : List Bool → List Arg → Bool
  | _, [] => true
  | passing, .value e :: args =>
    e.noEscape D N (passing.headD false) && argsNoEscape D N passing.tail args
  | passing, .inout ⟨x, path⟩ :: args =>
    !N.contains x && pathNoEscape D N path && argsNoEscape D N passing.tail args

/-- No parameter of `N` escapes from the indexes of a place. -/
def pathNoEscape (D : Decls) (N : List Name) : List Projection → Bool
  | [] => true
  | .field _ :: path => pathNoEscape D N path
  | .index i :: path => i.noEscape D N false && pathNoEscape D N path

/-- No parameter of `N` escapes from the arms of a `match`. -/
def armsNoEscape (D : Decls) (N : List Name) : List Arm → Bool
  | [] => true
  | ⟨_, binders, body⟩ :: arms =>
    body.noEscape D (N.removeAll binders) false && armsNoEscape D N arms

end

/-! ## A function without non-escaping parameters -/

mutual

theorem Expr.names_nil : ∀ e : Expr, e.names [] = false
  | .var _ | .move _ => rfl
  | .int _ | .bool _ | .unit | .break | .continue | .fnRef _ _ _ | .method _ _ _ => rfl
  | .record _ _ fields => fieldsNames_nil fields
  | .variant _ _ _ es | .list _ es | .op _ es | .view es => exprsNames_nil es
  | .field e _ | .raise e | .perform _ e | .try e | .loop e | .return e => Expr.names_nil e
  | .index a b | .seq a b | .withH _ _ a b | .while a b => by simp [Expr.names, Expr.names_nil a, Expr.names_nil b]
  | .held _ hs b => by simp [Expr.names, exprsNames_nil hs, Expr.names_nil b]
  | .closure _ _ _ body => by simp [Expr.names, Expr.names_nil body]
  | .call f args _ => by simp [Expr.names, Expr.names_nil f, argsNames_nil args]
  | .letIn _ _ a b | .varIn _ _ a b | .for _ _ a b | .tryCatch a _ _ b _ => by
    simp [Expr.names, Expr.names_nil a, Expr.names_nil b]
  | .assign ⟨_, path⟩ v => by simp [Expr.names, pathNames_nil path, Expr.names_nil v]
  | .if c _ a b => by simp [Expr.names, Expr.names_nil c, Expr.names_nil a, Expr.names_nil b]
  | .match e _ arms => by simp [Expr.names, Expr.names_nil e, armsNames_nil arms]

theorem exprsNames_nil : ∀ es : List Expr, exprsNames [] es = false
  | [] => rfl
  | e :: es => by simp [exprsNames, Expr.names_nil e, exprsNames_nil es]

theorem fieldsNames_nil : ∀ fields : List (Name × Expr), fieldsNames [] fields = false
  | [] => rfl
  | (_, e) :: fields => by simp [fieldsNames, Expr.names_nil e, fieldsNames_nil fields]

theorem argsNames_nil : ∀ args : List Arg, argsNames [] args = false
  | [] => rfl
  | .value e :: args => by simp [argsNames, Expr.names_nil e, argsNames_nil args]
  | .inout ⟨_, path⟩ :: args => by simp [argsNames, pathNames_nil path, argsNames_nil args]

theorem pathNames_nil : ∀ path : List Projection, pathNames [] path = false
  | [] => rfl
  | .field _ :: path => pathNames_nil path
  | .index i :: path => by simp [pathNames, Expr.names_nil i, pathNames_nil path]

theorem armsNames_nil : ∀ arms : List Arm, armsNames [] arms = false
  | [] => rfl
  | ⟨_, _, body⟩ :: arms => by
    simp [armsNames, Expr.names_nil body, armsNames_nil arms]

end

mutual

theorem Expr.noEscape_nil (D : Decls) (allowed : Bool) :
    ∀ e : Expr, e.noEscape D [] allowed = true
  | .var _ | .move _ => by simp [Expr.noEscape]
  | .int _ | .bool _ | .unit | .break | .continue | .fnRef _ _ _ | .method _ _ _ => rfl
  | .record _ _ fields => fieldsNoEscape_nil D fields
  | .variant _ _ _ es | .list _ es | .op _ es | .view es => exprsNoEscape_nil D es
  | .field e _ | .raise e | .perform _ e | .try e | .loop e | .return e => Expr.noEscape_nil D false e
  | .index a b | .seq a b | .withH _ _ a b | .while a b => by
    simp [Expr.noEscape, Expr.noEscape_nil D false a, Expr.noEscape_nil D false b]
  | .held _ hs b => by simp [Expr.noEscape, exprsNoEscape_nil D hs, Expr.noEscape_nil D false b]
  | .closure _ _ _ body => by simp [Expr.noEscape, Expr.noEscape_nil D false body, Expr.names_nil]
  | .call f args _ => by simp [Expr.noEscape, Expr.noEscape_nil D true f, argsNoEscape_nil D]
  | .letIn _ _ a b | .varIn _ _ a b | .for _ _ a b | .tryCatch a _ _ b _ => by
    simp [Expr.noEscape, Expr.noEscape_nil D false a, Expr.noEscape_nil D false b]
  | .assign ⟨_, path⟩ v => by
    simp [Expr.noEscape, pathNoEscape_nil D path, Expr.noEscape_nil D false v]
  | .if c _ a b => by
    simp [Expr.noEscape, Expr.noEscape_nil D false c, Expr.noEscape_nil D false a,
      Expr.noEscape_nil D false b]
  | .match e _ arms => by simp [Expr.noEscape, Expr.noEscape_nil D false e, armsNoEscape_nil D arms]

theorem exprsNoEscape_nil (D : Decls) : ∀ es : List Expr, exprsNoEscape D [] es = true
  | [] => rfl
  | e :: es => by simp [exprsNoEscape, Expr.noEscape_nil D false e, exprsNoEscape_nil D es]

theorem fieldsNoEscape_nil (D : Decls) :
    ∀ fields : List (Name × Expr), fieldsNoEscape D [] fields = true
  | [] => rfl
  | (_, e) :: fields => by
    simp [fieldsNoEscape, Expr.noEscape_nil D false e, fieldsNoEscape_nil D fields]

theorem argsNoEscape_nil (D : Decls) :
    ∀ (passing : List Bool) (args : List Arg), argsNoEscape D [] passing args = true
  | _, [] => by simp [argsNoEscape]
  | passing, .value e :: args => by
    simp [argsNoEscape, Expr.noEscape_nil D _ e, argsNoEscape_nil D _ args]
  | passing, .inout ⟨_, path⟩ :: args => by
    simp [argsNoEscape, pathNoEscape_nil D path, argsNoEscape_nil D _ args]

theorem pathNoEscape_nil (D : Decls) : ∀ path : List Projection, pathNoEscape D [] path = true
  | [] => rfl
  | .field _ :: path => pathNoEscape_nil D path
  | .index i :: path => by
    simp [pathNoEscape, Expr.noEscape_nil D false i, pathNoEscape_nil D path]

theorem armsNoEscape_nil (D : Decls) : ∀ arms : List Arm, armsNoEscape D [] arms = true
  | [] => rfl
  | ⟨_, _, body⟩ :: arms => by
    simp [armsNoEscape, Expr.noEscape_nil D false body, armsNoEscape_nil D arms]

end

/-- No non-escaping parameter of a function escapes from its body (effects.no-escape). -/
def FnDecl.NoEscape (D : Decls) (d : FnDecl) : Prop :=
  d.body.noEscape D d.nonEscaping false = true

/-- No function of a program lets a non-escaping parameter escape. `main` has
no parameters. -/
def Program.NoEscape (p : Program) : Prop :=
  ∀ d ∈ p.decls.fns, d.NoEscape p.decls

/-- A function without non-escaping parameters lets none escape. -/
theorem FnDecl.noEscape_of_nil {D : Decls} {d : FnDecl} (h : d.nonEscaping = []) :
    d.NoEscape D := by
  unfold FnDecl.NoEscape
  rw [h]
  exact Expr.noEscape_nil D false d.body

end Stilt
