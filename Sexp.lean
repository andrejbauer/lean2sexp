import Lean

inductive Sexp : Type
| atom : String → Sexp
| string : String → Sexp
| integer : Int → Sexp
| double : Float → Sexp
| cons : List Sexp → Sexp

partial def Sexp.toString : Sexp → String
  | .atom s => s
  | .string s => s.quote
  | .integer k => ToString.toString k
  | .double x => ToString.toString x
  | .cons lst => "(" ++ (" ".intercalate $ lst.map toString) ++ ")"

instance: ToString Sexp where
  toString := Sexp.toString

def constr (head : String) (lst : List Sexp) : Sexp :=
  .cons ((.atom (":" ++ head)) :: lst)

class Sexpable (α : Type) : Type where
  toSexp : α → Sexp

def toSexp {α : Type} [s : Sexpable α] (x : α): Sexp := s.toSexp x

instance: Sexpable String where
  toSexp := .string

instance: Sexpable Int where
  toSexp := .integer

instance: Sexpable Nat where
  toSexp := fun n => .integer ↑n

instance: Sexpable UInt64 where
  toSexp := fun k => .integer ↑k.val

instance: Sexpable Float where
  toSexp := .double

def Sexp.fromName (n : Lean.Name) : Sexp :=
  match n with
  | .anonymous => constr "anonymous" []
  | .str mdl nm =>
    constr "name" $ (toSexp mdl.hash) :: (toSexp nm.hash) :: (toAtoms n).reverse
  | .num mdl k =>
    constr "name" $ (toSexp mdl.hash) :: (toSexp k) :: (toAtoms n).reverse
  where
    toAtoms (n : Lean.Name) : List Sexp :=
      match n with
      | .anonymous => [.atom "_"]
      | .str .anonymous s => [.atom s]
      | .str mdl s => .atom s :: toAtoms mdl
      | .num mdl k => .atom s!"num{k}" :: toAtoms mdl

instance: Sexpable Lean.Name where
  toSexp := Sexp.fromName

def Sexp.fromLevel (lvl : Lean.Level) : Sexp := constr "level" [fromLvl lvl]
  where
    fromLvl : Lean.Level → Sexp
    | .zero => constr "lzero" []
    | .succ lvl =>  constr "lsucc" [fromLevel lvl]
    | .max lvl1 lvl2 => constr "max" [fromLevel lvl1, fromLevel lvl2]
    | .imax lvl1 lvl2 => constr "imax" [fromLevel lvl1, fromLevel lvl2]
    | .param nm => toSexp nm
    | .mvar mv => toSexp mv.name

instance: Sexpable Lean.Level where
  toSexp := Sexp.fromLevel

instance: Sexpable Lean.BinderInfo where
  toSexp := fun info =>
    match info with
    | .default => constr "default" []
    | .implicit => constr "implicit" []
    | .strictImplicit => constr "strict-implicit" []
    | .instImplicit => constr "inst-implicit" []

instance: Sexpable Lean.Literal where
  toSexp := fun lit =>
    match lit with
    | .natVal val => constr "literal" [toSexp val]
    | .strVal val => constr "literal" [toSexp val]

def Sexp.fromExpr : Lean.Expr → Sexp
  | .bvar k => constr "var" [toSexp k]
  | .fvar fv => toSexp fv.name
  | .mvar mvarId => constr "meta" [toSexp mvarId.name.hash]
  | .sort u => constr "sort" [toSexp u]
  | .const declName us => constr "const" $ toSexp declName :: us.map toSexp
  | .app e1 e2 => constr "apply" [fromExpr e1, fromExpr e2]
  | .lam _ binderType body _ =>
    constr "lambda" [fromExpr binderType, fromExpr body]
  | .forallE _ binderType body _ =>
    constr "pi" [fromExpr binderType, fromExpr body]
  | .letE declName type value body _ =>
    constr "let" [toSexp declName, fromExpr type, fromExpr value, fromExpr body]
  | .lit l => toSexp l
  | .mdata _ expr => fromExpr expr
  | .proj typeName idx struct => constr "proj" [toSexp typeName, toSexp idx, fromExpr struct]

instance: Sexpable Lean.Expr where
  toSexp := Sexp.fromExpr

instance: Sexpable Lean.QuotKind where
  toSexp := fun k =>
    match k with
  | .type => constr "type" []
  | .ctor => constr "ctor" []
  | .lift => constr "lift" []
  | .ind  => constr "ind" []

instance: Sexpable Lean.ConstantInfo where
  toSexp := fun info =>
    constr "definition" [toSexp info.name, toSexp info.type, theDef info]
    where theDef : Lean.ConstantInfo → Sexp := fun info =>
      match info with
      | .axiomInfo _ => constr "axiom" []
      | .defnInfo val => constr "function" [toSexp val.value]
      | .thmInfo val => constr "function" [toSexp val.value]
      | .opaqueInfo val => constr "abstract" [toSexp val.value]
      | .quotInfo val => constr "quot-info" [toSexp val.kind, toSexp val.toConstantVal.name]
      | .inductInfo val => constr "data" $ toSexp val.type :: val.ctors.map toSexp
      | .ctorInfo val => constr "constructor" [toSexp val.induct]
      | .recInfo val => constr "recursor" [toSexp val.type]

def Sexp.fromModuleData (nm : Lean.Name) (data : Lean.ModuleData) : Sexp :=
  constr "module" $ constr "module-name" [toSexp nm] :: (data.constants.toList.filter keepEntry).map toSexp
  where keepEntry (info : Lean.ConstantInfo) : Bool :=
    match info.name with
    | .anonymous => true
    | .str _ s => ! "_cstage".isPrefixOf s && ! "_spec".isPrefixOf s
    | .num _ k => true
