import LeanTs.Json
import LeanTs.Core

/-!
# Js

The AST of the JavaScript to emit, and the ESM / `.d.ts` printers.

Parentheses are always written, without consulting precedence. A precedence table would go on the
compiler's trusted base while buying nothing in Phase 1. Readable output is Phase 3's problem.
-/

namespace LeanTs.Js

/-- A type expanded into what the generated code needs in order to check a value against it at runtime.
`Ty.named` is resolved away here rather than emitting a table of type definitions, so a function carries
only the shapes it actually accepts and a bundler can still drop the ones nobody imported. -/
inductive TyDesc where
  | bool
  | int53
  | uint32
  | string
  | bigint
  | option (t : TyDesc)
  | result (ok err : TyDesc)
  | array (t : TyDesc)
  | dict (value : TyDesc)
  | ctors (alts : List (String × List (String × TyDesc)))
  deriving Inhabited, BEq

mutual

/-- The descriptor the entry check reads. Total for the reason `Expr.render` is: the text the artifact
carries has to be something a proof can unfold. -/
def TyDesc.render : TyDesc → String
  | .bool => "[\"bool\"]"
  | .int53 => "[\"int53\"]"
  | .uint32 => "[\"uint32\"]"
  | .string => "[\"string\"]"
  | .bigint => "[\"bigint\"]"
  | .option t => "[\"option\", " ++ t.render ++ "]"
  | .result ok err => "[\"result\", " ++ ok.render ++ ", " ++ err.render ++ "]"
  | .array t => "[\"array\", " ++ t.render ++ "]"
  | .dict v => "[\"dict\", " ++ v.render ++ "]"
  | .ctors alts => "[\"ctors\", [" ++ TyDesc.renderAlts alts ++ "]]"
termination_by d => sizeOf d

def TyDesc.renderFields : List (String × TyDesc) → String
  | [] => ""
  | [(n, d)] => "[\"" ++ escapeString n ++ "\", " ++ d.render ++ "]"
  | (n, d) :: rest =>
    "[\"" ++ escapeString n ++ "\", " ++ d.render ++ "], " ++ TyDesc.renderFields rest
termination_by fields => sizeOf fields

def TyDesc.renderAlts : List (String × List (String × TyDesc)) → String
  | [] => ""
  | [(c, fields)] => "[\"" ++ escapeString c ++ "\", [" ++ TyDesc.renderFields fields ++ "]]"
  | (c, fields) :: rest =>
    "[\"" ++ escapeString c ++ "\", [" ++ TyDesc.renderFields fields ++ "]], "
      ++ TyDesc.renderAlts rest
termination_by alts => sizeOf alts

end

/-- A comma-separated list of names. Written as a recursion rather than `String.intercalate`, which walks
an accumulator and does not unfold in a proof, for the reason the rest of the printer is: the file the
compiler writes has to be something a proof can read back. -/
def renderNames : List String → String
  | [] => ""
  | [n] => n
  | n :: rest => n ++ ", " ++ renderNames rest

inductive Expr where
  | num (i : Int)
  | bigLit (i : Int)
  | str (s : String)
  | bool (b : Bool)
  | ident (name : String)
  | unary (op : String) (e : Expr)
  | binary (op : String) (lhs rhs : Expr)
  | cond (c t e : Expr)
  | call (callee : String) (args : List Expr)
  | arrowCall (params : List String) (body : Expr) (args : List Expr)
  | objLit (fields : List (String × Expr))
  | member (obj : Expr) (field : String)
  | arrayLit (items : List Expr)
  | dictLit (entries : List (String × Expr))
  | check (d : TyDesc) (e : Expr)
  | mapJs (arr : Expr) (binder : String) (body : Expr)
  | filterJs (arr : Expr) (binder : String) (body : Expr)
  | findJs (arr : Expr) (binder : String) (body : Expr)
  | quantJs (op : Core.QuantOp) (arr : Expr) (binder : String) (body : Expr)
  | reduceJs (arr init : Expr) (accName elemName : String) (body : Expr)
  deriving Inhabited, BEq

inductive Stmt where
  | const (name : String) (val : Expr)
  | ret (e : Expr)
  deriving Inhabited, BEq

structure Func where
  name : String
  params : List String
  body : List Stmt
  doc : String
  exported : Bool
  deriving Inhabited, BEq

structure Module where
  funcs : List Func
  deriving Inhabited, BEq

mutual

/-- The text the module carries. Written as a mutual recursion over the lists rather than `partial`, so
a proof about the file the compiler writes can unfold it. -/
def Expr.render : Expr → String
  | .num i => renderInt i
  | .bigLit i => renderInt i ++ "n"
  | .str s => "\"" ++ escapeString s ++ "\""
  | .bool b => if b then "true" else "false"
  | .ident name => name
  | .unary op e => "(" ++ op ++ e.render ++ ")"
  | .binary op lhs rhs => "(" ++ lhs.render ++ " " ++ op ++ " " ++ rhs.render ++ ")"
  | .cond c t e => "(" ++ c.render ++ " ? " ++ t.render ++ " : " ++ e.render ++ ")"
  | .call callee args => callee ++ "(" ++ Expr.renderList args ++ ")"
  | .arrowCall params body args =>
    "((" ++ renderNames params ++ ") => (" ++ body.render ++ "))("
      ++ Expr.renderList args ++ ")"
  | .objLit fields => "{ " ++ Expr.renderFields fields ++ " }"
  | .member obj field => "(" ++ obj.render ++ ")." ++ field
  | .arrayLit items => "[" ++ Expr.renderList items ++ "]"
  | .dictLit entries => "new Map([" ++ Expr.renderEntries entries ++ "])"
  | .check d e => "__ck(" ++ e.render ++ ", " ++ d.render ++ ")"
  | .mapJs arr binder body =>
    "__map(" ++ arr.render ++ ", (" ++ binder ++ ") => (" ++ body.render ++ "))"
  | .filterJs arr binder body =>
    "__filter(" ++ arr.render ++ ", (" ++ binder ++ ") => (" ++ body.render ++ "))"
  | .findJs arr binder body =>
    "__find(" ++ arr.render ++ ", (" ++ binder ++ ") => (" ++ body.render ++ "))"
  | .quantJs op arr binder body =>
    "__" ++ op.name ++ "(" ++ arr.render ++ ", (" ++ binder ++ ") => (" ++ body.render ++ "))"
  | .reduceJs arr init accName elemName body =>
    "__reduce(" ++ arr.render ++ ", " ++ init.render ++ ", (" ++ accName ++ ", " ++ elemName
      ++ ") => (" ++ body.render ++ "))"
termination_by e => sizeOf e

def Expr.renderList : List Expr → String
  | [] => ""
  | [e] => e.render
  | e :: rest => e.render ++ ", " ++ Expr.renderList rest
termination_by es => sizeOf es

def Expr.renderFields : List (String × Expr) → String
  | [] => ""
  | [(k, v)] => "\"" ++ escapeString k ++ "\": " ++ v.render
  | (k, v) :: rest => "\"" ++ escapeString k ++ "\": " ++ v.render ++ ", " ++ Expr.renderFields rest
termination_by fields => sizeOf fields

def Expr.renderEntries : List (String × Expr) → String
  | [] => ""
  | [(k, v)] => "[\"" ++ escapeString k ++ "\", " ++ v.render ++ "]"
  | (k, v) :: rest =>
    "[\"" ++ escapeString k ++ "\", " ++ v.render ++ "], " ++ Expr.renderEntries rest
termination_by entries => sizeOf entries

end

def Stmt.render : Stmt → String
  | .const name val => "  const " ++ name ++ " = " ++ val.render ++ ";"
  | .ret e => "  return " ++ e.render ++ ";"

def Stmt.renderAll : List Stmt → String
  | [] => ""
  | [s] => s.render
  | s :: rest => s.render ++ "\n" ++ Stmt.renderAll rest

def Func.render (f : Func) : String :=
  let header := if f.doc.isEmpty then "" else "/** " ++ f.doc ++ " */\n"
  let keyword := if f.exported then "export function " else "function "
  header ++ keyword ++ f.name ++ "(" ++ renderNames f.params ++ ") {\n"
    ++ Stmt.renderAll f.body ++ "\n}"

/-- The runtime helpers the generated code calls. The operations where JS and Lean split on the answer
are confined here. -/
def runtime : String :=
"const __fail = (code) => {
  const error = new Error(code);
  error.code = code;
  throw error;
};

// Int53 is a mathematical integer, so no -0 survives. In JS both 0 - 0 and -4 % 2 are -0.
const __i53 = (x) =>
  Number.isSafeInteger(x) ? (x === 0 ? 0 : x) : __fail(\"int53Overflow\");

// Math.trunc(a / b) is off by one when a is near 2^53. Integer division avoids floating-point division.
const __i53div = (a, b) =>
  b === 0 ? __fail(\"divByZero\") : Number(BigInt(a) / BigInt(b));

const __i53mod = (a, b) => (b === 0 ? __fail(\"divByZero\") : __i53(a % b));

const __u32mul = (a, b) => Math.imul(a, b) >>> 0;

const __u32div = (a, b) => (b === 0 ? __fail(\"divByZero\") : Math.trunc(a / b) >>> 0);

const __u32mod = (a, b) => (b === 0 ? __fail(\"divByZero\") : a % b >>> 0);

const __bigdiv = (a, b) => (b === 0n ? __fail(\"divByZero\") : a / b);

const __bigmod = (a, b) => (b === 0n ? __fail(\"divByZero\") : a % b);

// Math.abs, Math.min and Math.max throw on a BigInt, so the comparisons are written out instead.
const __abs = (x) => (x < 0 ? -x : x);

const __min = (a, b) => (a <= b ? a : b);

const __max = (a, b) => (a <= b ? b : a);

const __strcmp = (a, b) => {
  const x = Array.from(a);
  const y = Array.from(b);
  const n = Math.min(x.length, y.length);
  for (let i = 0; i < n; i++) {
    const d = x[i].codePointAt(0) - y[i].codePointAt(0);
    if (d !== 0) return d < 0 ? -1 : 1;
  }
  return x.length === y.length ? 0 : x.length < y.length ? -1 : 1;
};

const __chars = (s) => Array.from(s);

const __strlen = (s) => __chars(s).length;

// JS's own trim also strips NBSP, the BOM and the line separators; eval strips only these four.
const __trim = (s) => {
  const xs = __chars(s);
  const ws = (c) => c === \" \" || c === \"\\t\" || c === \"\\n\" || c === \"\\r\";
  let i = 0;
  let j = xs.length;
  while (i < j && ws(xs[i])) i++;
  while (j > i && ws(xs[j - 1])) j--;
  return xs.slice(i, j).join(\"\");
};

// toUpperCase is not ASCII: it maps \"ß\" to \"SS\", changing the length of the string.
const __upper = (s) =>
  __chars(s)
    .map((c) => (c >= \"a\" && c <= \"z\" ? c.toUpperCase() : c))
    .join(\"\");

const __lower = (s) =>
  __chars(s)
    .map((c) => (c >= \"A\" && c <= \"Z\" ? c.toLowerCase() : c))
    .join(\"\");

// Native, unlike the four above: UTF-16 preserves prefixes and suffixes and no argument can hold a lone
// surrogate, so a match on units is a match on code points.
const __startsWith = (s, t) => s.startsWith(t);

const __endsWith = (s, t) => s.endsWith(t);

const __includes = (s, t) => s.includes(t);

// split(\"\") returns the UTF-16 units, where eval returns the whole string.
const __split = (s, sep) => (sep === \"\" ? [s] : s.split(sep));

// Indices count code points, and one outside the string fails rather than being clamped.
const __substring = (s, lo, hi) => {
  const xs = __chars(s);
  return Number.isSafeInteger(lo) &&
    Number.isSafeInteger(hi) &&
    lo >= 0 &&
    hi >= lo &&
    hi <= xs.length
    ? xs.slice(lo, hi).join(\"\")
    : __fail(\"indexOutOfBounds\");
};

// Bounds outside the array fail rather than being clamped, the way an index read does.
const __aslice = (xs, lo, hi) =>
  Number.isSafeInteger(lo) &&
  Number.isSafeInteger(hi) &&
  lo >= 0 &&
  hi >= lo &&
  hi <= xs.length
    ? xs.slice(lo, hi)
    : __fail(\"indexOutOfBounds\");

const __aconcat = (a, b) => [...a, ...b];

// A fresh array: reverse() would otherwise write through to the caller's.
const __areverse = (xs) => [...xs].reverse();

const __dget = (d, k) => (d.has(k) ? { tag: \"some\", value: d.get(k) } : { tag: \"none\" });

const __dhas = (d, k) => d.has(k);

// A fresh Map: values in the subset are immutable, so set cannot write through to the caller's.
const __dset = (d, k, v) => new Map(d).set(k, v);

const __dkeys = (d) => Array.from(d.keys());

const __dvalues = (d) => Array.from(d.values());

const __ddelete = (d, k) => new Map([...d].filter(([key]) => key !== k));

// === compares references, so it is unusable on constructor values and arrays.
const __eq = (a, b) => {
  if (a === b) return true;
  if (typeof a !== \"object\" || typeof b !== \"object\" || a === null || b === null) return false;
  if (a instanceof Map || b instanceof Map) {
    if (!(a instanceof Map) || !(b instanceof Map) || a.size !== b.size) return false;
    const xs = Array.from(a);
    const ys = Array.from(b);
    return xs.every(([k, v], i) => ys[i][0] === k && __eq(v, ys[i][1]));
  }
  if (Array.isArray(a) || Array.isArray(b)) {
    return (
      Array.isArray(a) &&
      Array.isArray(b) &&
      a.length === b.length &&
      a.every((x, i) => __eq(x, b[i]))
    );
  }
  const keys = Object.keys(a);
  return (
    keys.length === Object.keys(b).length &&
    keys.every((k) => Object.hasOwn(b, k) && __eq(a[k], b[k]))
  );
};

// An out-of-range index fails rather than yielding undefined. undefined does not exist in the subset.
const __at = (xs, i) =>
  Number.isSafeInteger(i) && i >= 0 && i < xs.length
    ? xs[i]
    : __fail(\"indexOutOfBounds\");

const __map = (xs, f) => {
  const out = [];
  for (let i = 0; i < xs.length; i++) out.push(f(xs[i]));
  return out;
};

const __filter = (xs, f) => {
  const out = [];
  for (let i = 0; i < xs.length; i++) if (f(xs[i])) out.push(xs[i]);
  return out;
};

// Stops at the first element the predicate accepts, so a predicate that would trap later never runs.
const __find = (xs, f) => {
  for (let i = 0; i < xs.length; i++) if (f(xs[i])) return { tag: \"some\", value: xs[i] };
  return { tag: \"none\" };
};

const __all = (xs, f) => {
  for (let i = 0; i < xs.length; i++) if (!f(xs[i])) return false;
  return true;
};

const __any = (xs, f) => {
  for (let i = 0; i < xs.length; i++) if (f(xs[i])) return true;
  return false;
};

const __reduce = (xs, init, f) => {
  let acc = init;
  for (let i = 0; i < xs.length; i++) acc = f(acc, xs[i]);
  return acc;
};

const __isObj = (x) => typeof x === \"object\" && x !== null && !Array.isArray(x);

// Fields are compared in order and by count, because eval compares them that way: a missing field, an
// extra one and a reordering are all type errors.
const __hasFields = (x, fields) => {
  const keys = Object.keys(x);
  if (keys.length !== fields.length + 1) return false;
  for (let i = 0; i < fields.length; i++) {
    if (keys[i + 1] !== fields[i][0] || !__has(x[fields[i][0]], fields[i][1])) return false;
  }
  return true;
};

const __has = (x, t) => {
  switch (t[0]) {
    case \"bool\":
      return typeof x === \"boolean\";
    case \"int53\":
      return typeof x === \"number\" && Number.isSafeInteger(x);
    case \"uint32\":
      return typeof x === \"number\" && Number.isInteger(x) && x >= 0 && x <= 4294967295;
    case \"string\":
      return typeof x === \"string\";
    case \"bigint\":
      return typeof x === \"bigint\";
    case \"array\":
      return Array.isArray(x) && x.every((e) => __has(e, t[1]));
    case \"dict\":
      return (
        x instanceof Map &&
        Array.from(x.keys()).every((k) => typeof k === \"string\") &&
        Array.from(x.values()).every((e) => __has(e, t[1]))
      );
    case \"option\":
      return (
        __isObj(x) &&
        (x.tag === \"none\"
          ? __hasFields(x, [])
          : x.tag === \"some\" && __hasFields(x, [[\"value\", t[1]]]))
      );
    case \"result\":
      return (
        __isObj(x) &&
        (x.tag === \"ok\"
          ? __hasFields(x, [[\"value\", t[1]]])
          : x.tag === \"error\" && __hasFields(x, [[\"error\", t[2]]]))
      );
    default: {
      if (!__isObj(x)) return false;
      const alt = t[1].find((a) => a[0] === x.tag);
      return alt !== undefined && __hasFields(x, alt[1]);
    }
  }
};

// Validates without normalising, unlike __i53. A -0 argument is a safe integer, and every answer built
// from it passes through __i53 or a comparison that already treats -0 and 0 alike, so normalising here
// would change nothing a caller can observe.
const __ck = (x, t) => (__has(x, t) ? x : __fail(\"typeError\"));"

def Func.renderAll : List Func → String
  | [] => ""
  | f :: rest => f.render ++ "\n\n" ++ Func.renderAll rest

/-- The text of the file the compiler writes, source-map link and all. -/
def Module.render (m : Module) : String :=
  "// Generated by leants. Do not edit.\n\n" ++ runtime ++ "\n\n"
    ++ Func.renderAll m.funcs ++ "//# sourceMappingURL=index.js.map\n"

mutual

/-- The type the `.d.ts` gives a value of this type. Total for the reason the renderers are: the file the
compiler writes has to be something a proof can unfold. -/
def tsType : Core.Ty → String
  | .bool => "boolean"
  | .int53 => "number"
  | .uint32 => "number"
  | .string => "string"
  | .bigint => "bigint"
  | .var n => n
  | .named n [] => n
  | .named n args => n ++ "<" ++ tsTypeList args ++ ">"
  | .option t => "Option<" ++ tsType t ++ ">"
  | .result ok err => "Result<" ++ tsType ok ++ ", " ++ tsType err ++ ">"
  | .array t => "readonly " ++ tsType t ++ "[]"
  | .dict v => "ReadonlyMap<string, " ++ tsType v ++ ">"
  | .fn params ret => "(" ++ tsParams 0 params ++ ") => " ++ tsType ret
termination_by ty => sizeOf ty

def tsTypeList : List Core.Ty → String
  | [] => ""
  | [t] => tsType t
  | t :: rest => tsType t ++ ", " ++ tsTypeList rest
termination_by ts => sizeOf ts

def tsParams (i : Nat) : List Core.Ty → String
  | [] => ""
  | [t] => s!"a{i}: {tsType t}"
  | t :: rest => s!"a{i}: {tsType t}, " ++ tsParams (i + 1) rest
termination_by ts => sizeOf ts

end

private def renderCtor (c : Core.CtorDef) : String :=
  let fields := c.fields.map fun f => s!"; readonly {f.name}: {tsType f.ty}"
  "{ readonly tag: \"" ++ c.name ++ "\"" ++ String.join fields ++ " }"

private def declareType (t : Core.TypeDef) : String :=
  let head :=
    if t.params.isEmpty then t.name
    else t.name ++ "<" ++ String.intercalate ", " t.params ++ ">"
  match t.ctors.map renderCtor with
  | [only] => "export type " ++ head ++ " = " ++ only ++ ";"
  | ctors => "export type " ++ head ++ " =\n  | " ++ String.intercalate "\n  | " ctors ++ ";"

def declareFunc (d : Core.Decl) : String :=
  let params := d.params.map fun p => p.name ++ ": " ++ tsType p.ty
  "export declare function " ++ d.name ++ "(" ++ String.intercalate ", " params ++ "): "
    ++ tsType d.ret ++ ";"

/-- `Option` and `Result` are built in, so their declarations always come along. Types are erased, so an
unused one is harmless. -/
private def builtinTypes : String :=
"export type Option<T> =
  | { readonly tag: \"none\" }
  | { readonly tag: \"some\"; readonly value: T };

export type Result<T, E> =
  | { readonly tag: \"ok\"; readonly value: T }
  | { readonly tag: \"error\"; readonly error: E };"

def renderDts (p : Core.Program) : String :=
  let sections :=
    [builtinTypes] ++ p.types.map declareType ++ p.publicDecls.map declareFunc
  "// Generated by leants. Do not edit.\n\n" ++ String.intercalate "\n\n" sections ++ "\n"

end LeanTs.Js
