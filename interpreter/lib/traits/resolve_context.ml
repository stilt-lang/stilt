(* The state of name resolution, the scopes of modules, and the contexts in
   which names are resolved. *)

open Hir
module Smap = Map.Make (String)
module Sset = Set.Make (String)

let prelude = "std.prelude"

(* lexical.primitive-type-names *)
let primitive_types = Lexicon.primitive_types
let is_primitive name = List.mem name primitive_types
let dotted segments = String.concat "." segments
let dotted_path (path : name list) = dotted (List.map (fun n -> n.desc) path)

(* State *)

type reference = { from : string; target : string; file : string; loc : loc }

(* An E0211 in a body, for a name as written. A deferred one is a name that a
   pattern writes without a module, whose failure only type checking finds
   (patterns.floats). *)
type unknown = { written : string; diagnostic : Diagnostic.t; deferred : bool }

(* A pattern macro (macros.checked-templates). *)
type macro = {
  decl : Ast.syntax_decl;
  home : string;
  usable : bool;
  expr : bool;
  pattern : bool;
  named : (item * loc) list;
}

type state = {
  mutable diagnostics : Diagnostic.t list;
  mutable unknown_names : unknown list option;
  mutable unresolved : (string * loc) list;
  mutable held : (string * loc * string * Diagnostic.t) list;
      (* Each E0211 held back for type checking, with its file, its body and
         its name. *)
  mutable references : reference list;
  mutable advanced : string list;
  mutable next_id : int;
  macros : (item, macro) Hashtbl.t;
  expansions : (int, string) Hashtbl.t;
  mutable chain : string list;
  mutable declaring : bool;
  mutable named : (item * loc) list option;
  mutable meta : string list;
  mutable systems : string list;
  constants : (item, Ast.const_decl * string) Hashtbl.t;
      (* Each constant's declaration and the module whose scope its value is
         read in, by the constant, or by its type and name for one of an
         inherent impl, so that a value argument can name it (generics.constant-arguments). *)
  computed : (item, computed) Hashtbl.t;
  host : Procs.host;
}

(* generics.constant-arguments: what computing a constant given as a value argument
   gives: its type's name and its value in decimal, or a panic, or nothing,
   for a constant with an error of its own. *)
and computed =
  | Value of string * string
  | Panics of string
  | Unknown of string option

let report st ~file code (loc : loc) fmt =
  Printf.ksprintf
    (fun message ->
      let d =
        { Diagnostic.code; file; line = loc.line; col = loc.col; message }
      in
      st.diagnostics <- d :: st.diagnostics)
    fmt

(* Scopes (declarations.namespaces) *)

type kind =
  | Type_item
  | Trait_item
  | Fn_item
  | Const_item
  | Variant_item
  | Macro_item
  | Proc_item
  | Effect_item

type entry = {
  kind : kind;
  pub : bool;
  arity : int;
      (* A type's number of type parameters, and a constructor trait's arity,
         which is 0 for a trait over types (traits.constructor-traits). *)
  params : string list; (* A trait's parameters (traits.trait-parameters). *)
  pack : bool;
      (* Whether a type's last parameter is a pack, which the arguments after
         the others give (variadics.packs and variadics.pack-inference). *)
  values : (int * string option) list;
      (* The positions of a type's value parameters, each with the name of
         its type when that is an integer type or [bool] (generics.value-parameters). *)
  advanced : bool;
      (* Whether a trait has parameters, functions without [self],
         constants or a constructor [Self], so that declaring, implementing
         or naming it in a bound makes a module advanced (traits.advanced-tier). *)
}

let entry ?(arity = 0) ?(params = []) ?(pack = false) ?(values = [])
    ?(advanced = false) kind pub =
  { kind; pub; arity; params; pack; values; advanced }

type value = Item of entry | Import of string | Import_error
type namespace = Types | Values

type scope = {
  name : string;
  file : string;
  types : entry Smap.t;
  values : value Smap.t;
  shadowed : Sset.t * Sset.t;
  unknown : Sset.t * Sset.t;
  metas : string Smap.t;
      (* The modules that [meta use] declarations name, by the names they
         bind (macros.meta-use). *)
}

type lookup = Found of string | Unnamed | Foreign of string | Missing

type env = {
  st : state;
  modules : Sset.t;
  scopes : scope Smap.t;
  namespaces : Sset.t;
  unnamed : Sset.t;
  view : int -> string -> lookup;
  items : Sset.t Smap.t;
}

let whole_view env name =
  if Sset.mem name env.namespaces then Found name
  else if Sset.mem name env.unnamed then Unnamed
  else Missing

let describe = function
  | Type_item -> "a type"
  | Trait_item -> "a trait"
  | Fn_item -> "a function"
  | Const_item -> "a constant"
  | Variant_item -> "a variant"
  | Macro_item -> "a macro"
  | Proc_item -> "a procedural macro"
  | Effect_item -> "an effect"

let is_type_kind = function
  | Type_item | Trait_item | Effect_item -> true
  | Fn_item | Const_item | Variant_item | Macro_item | Proc_item -> false

(* Contexts *)

type self = No_self | Impl_self of ty | Trait_self

(* Inside a quote, how a splice's expression is resolved in the code of the
   macro, and that code's locals (macros.splices and macros.quote-hygiene). *)
type quoting = { splice : place -> Ast.expr -> unit; outer : string list }

type ctx = {
  env : env;
  scope : scope;
  self : self;
  type_params : (string * var) list;
  kinds : (int * int) list;
      (* The constructor parameters in scope, by id, with their arities
         (traits.constructor-parameters). *)
  packs : int list; (* The packs in scope, by id (variadics.packs). *)
  misplaced : int list;
      (* The packs declared where none may be, by id, which E0344 reports and
         which are plain type parameters after it. *)
  spread : var list ref option;
      (* Inside a spread in a type, the packs it names so far. *)
  members : (int * (item * (string * ty) list) list) list;
      (* For each type parameter in scope, by id, the traits of its bounds,
         each with the types its arguments give the trait's parameters, which
         its member types name (traits.member-types). *)
  ctor : int;
      (* In a constructor trait or an impl of one, the trait's arity, and 0
         anywhere else (traits.constructor-traits and traits.constructor-impls). *)
  fixed : bool;
      (* Whether the functions here have the signatures of a trait: those of a
         trait or of a trait impl (traits.where). *)
  row_vars : (string * var) list;
  value_params : (string * (var * ty)) list;
      (* The value parameters in scope, with their types (generics.value-parameters-in-body). *)
  locals : (string * var option) list;
  in_loop : bool;
  public : bool;
  expanding : bool;
  quoting : quoting option;
  lost : bool;
      (* Whether a failed use of a procedural macro in a pattern opens the
         scope, so that a name that names nothing has the error type and is
         reported nowhere (macros.failed-uses). *)
}

let module_ctx env scope =
  {
    env;
    scope;
    self = No_self;
    type_params = [];
    kinds = [];
    packs = [];
    misplaced = [];
    spread = None;
    members = [];
    ctor = 0;
    fixed = false;
    row_vars = [];
    value_params = [];
    locals = [];
    in_loop = false;
    public = false;
    expanding = false;
    quoting = None;
    lost = false;
  }

(* views.std-view, projections.declaring-projection, and traits.advanced-tier: the module where the
   context is uses a feature of the advanced tier, unless it is a macro's
   expansion that uses it (macros.advanced-tier). *)
let advanced ctx =
  let st = ctx.env.st in
  if (not ctx.expanding) && not (List.mem ctx.scope.name st.advanced) then
    st.advanced <- ctx.scope.name :: st.advanced

(* generics.meta-tier, and meta.staging-tier: the module where the context is
   declares a value parameter or writes [comptime], which are features of the
   meta tier, unless it is a macro's expansion that does. *)
let meta ctx =
  let st = ctx.env.st in
  if (not ctx.expanding) && not (List.mem ctx.scope.name st.meta) then
    st.meta <- ctx.scope.name :: st.meta

(* c.systems-tier: the module where the context is declares a foreign
   function or writes an [unsafe] block, features of the systems tier, unless
   it is a macro's expansion that does. *)
let systems ctx =
  let st = ctx.env.st in
  if (not ctx.expanding) && not (List.mem ctx.scope.name st.systems) then
    st.systems <- ctx.scope.name :: st.systems

(* Runs [f], keeping none of the diagnostics it reports or the references it
   records, and tells whether it reported any. *)
let quietly st f =
  let diagnostics = st.diagnostics
  and unknown_names = st.unknown_names
  and references = st.references
  and advanced = st.advanced
  and meta = st.meta
  and systems = st.systems in
  st.unknown_names <- None;
  let reported = ref false in
  let restore () =
    reported := st.diagnostics != diagnostics;
    st.diagnostics <- diagnostics;
    st.unknown_names <- unknown_names;
    st.references <- references;
    st.advanced <- advanced;
    st.meta <- meta;
    st.systems <- systems
  in
  let result = Fun.protect ~finally:restore f in
  (result, !reported)

let errorf ctx code loc fmt =
  report ctx.env.st ~file:ctx.scope.file code loc fmt

let unknown_diagnostic ctx (loc : loc) message =
  {
    Diagnostic.code = Code.e0211;
    file = ctx.scope.file;
    line = loc.line;
    col = loc.col;
    message;
  }

(* macros.quote-hygiene: a quote that names a local of the macro's code means it
   through a splice. *)
let in_quote ctx name message =
  match ctx.quoting with
  | Some q when List.mem name q.outer ->
      Printf.sprintf
        "%s: `%s` is a local of the macro's code, which a quote names with \
         `$%s`"
        message name name
  | _ -> message

let unknown_name ctx ~name (loc : loc) fmt =
  Printf.ksprintf
    (fun message ->
      let st = ctx.env.st in
      let d = unknown_diagnostic ctx loc (in_quote ctx name message) in
      match st.unknown_names with
      | Some found ->
          st.unknown_names <-
            Some ({ written = name; diagnostic = d; deferred = false } :: found)
      | None -> st.diagnostics <- d :: st.diagnostics)
    fmt

(* Records that a pattern writes [name] without a module, where it means
   nothing in scope, which E0211 reports at [d] unless the type matched there
   has a variant of that name (patterns.unknown-variants). *)
let deferred_name ctx name d =
  let st = ctx.env.st in
  Option.iter
    (fun found ->
      st.unknown_names <-
        Some ({ written = name; diagnostic = d; deferred = true } :: found))
    st.unknown_names

(* Resolves the body known by [at] in [file] with [resolve], keeping one E0211
   for each name that doesn't resolve in it, at the place where that name
   starts first (errors.root-causes). For a name that a pattern also writes
   without a module, only type checking knows where that is, so that E0211 is
   held for it. *)
let in_body st ~file ~at resolve =
  let outer = st.unknown_names in
  st.unknown_names <- Some [];
  let resolved = resolve () in
  let found = Option.value st.unknown_names ~default:[] in
  st.unknown_names <- outer;
  let first = Hashtbl.create 8 in
  List.iter
    (fun u ->
      let (d : Diagnostic.t) = u.diagnostic in
      match Hashtbl.find_opt first u.written with
      | Some (e : Diagnostic.t)
        when compare (e.line, e.col) (d.line, d.col) <= 0 ->
          ()
      | _ -> if not u.deferred then Hashtbl.replace first u.written d)
    found;
  let deferred name = List.exists (fun u -> u.deferred && u.written = name) in
  Hashtbl.iter
    (fun name d ->
      if deferred name found then st.held <- (file, at, name, d) :: st.held
      else st.diagnostics <- d :: st.diagnostics)
    first;
  resolved

let fresh ctx (n : name) =
  let id = ctx.env.st.next_id in
  ctx.env.st.next_id <- id + 1;
  { id; name = n.desc; loc = n.loc }

let is_lower_identifier s =
  let is_letter = function 'a' .. 'z' | 'A' .. 'Z' -> true | _ -> false in
  let is_ident_char c = is_letter c || c = '_' || ('0' <= c && c <= '9') in
  s <> ""
  && String.for_all is_ident_char s
  && (not ('0' <= s.[0] && s.[0] <= '9'))
  &&
  match Seq.find is_letter (String.to_seq s) with
  | Some 'a' .. 'z' -> true
  | _ -> false

(* program.module-names *)
let valid_module_path = function
  | [] -> false
  | first :: _ as segments ->
      first <> "std"
      && List.for_all
           (fun s ->
             is_lower_identifier s
             && Option.is_none (Token.word s)
             && not (is_primitive s))
           segments
