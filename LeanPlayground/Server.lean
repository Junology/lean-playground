import Lean.Server
import Lean.Widget

open Lean Server

/-!
# Note on Lean server RPC

## Overview

The ***Remote Procedure Call (RPC)*** is a mechanism to allow a client to call procedures provided by the server.
In Lean LSP, the basic framework for RPC is provided in `Lean.Server.Rpc.Basic`, and it is used to implement interactive infoview UI.
Lean also allows user to define a new RPC method as a function of type

```lean
α → RequestM (RequestTask β)
```

In this note, we learn how to write a user-defined RPC method and how to use it from clients, especially via `#widget` command.

### Table of contents

* Definition and examples
* Use from widgets

### Convention

In this note, all codes are placed after
```lean
import Lean.Server

open Lean Server
```

### Acknowledgement and disclaimer

Most of the materials in the note are written based on the source code of the core modules `Lean.Server.Rpc.*` and the author's rough speculation.
In making a `#widget` example, [ProofWidgets](https://github.com/leanprover-community/ProofWidgets4) was a good reference.
Unfortunately, the official documentation about this topic is insufficient. 
As a result, the note may contain a lot of misunderstanding and wrong explanations.


## Definition and examples

### `RpcEncodable` structures

A ***server RPC method*** is a function of type

```lean
α → RequestM (RequestTask β)
```

The input type `α` and the output type `β` must be instances of the class

```lean
-- module: Lean.Server.Rpc.Basic

class RpcEncodable (α : Type) where
  rpcEncode : α → StateM RpcObjectStore Json
  rpcDecode : Json → ExceptT String (ReaderT RpcObjectStore Id) α
```

The point is that the data Lean server deals with must be representable in Json format.
In fact, an instance of `RpcEncodable` is automatically generated for any type `α` with `ToJson α` and `FromJson α`.
-/

/--
An example of `Json` representable structure.
`ColorfulText` carries a string data together with the size and the color.
-/
structure ColorfulText : Type where
  str : String
  color : UInt32
  deriving DecidableEq, Repr

instance : ToJson ColorfulText where
  toJson x := .mkObj [
    ("str", x.str),
    ("color", x.color.toNat)
  ]

instance : FromJson ColorfulText where
  fromJson? json := do
    let str ← json.getObjValAs? String "str"
    let color := UInt32.ofNat (← json.getObjValAs? Nat "color")
    return ⟨str,color⟩
 
/-!
Having instances of `ToJson ColorfulText` and `FromJson ColorfulText`, we can serialize/deserialize `ColorfulText` data to/from JSON format.

```lean
#eval toJson <| ColorfulText.mk "Hello" 0xDEADBE
/-
> {"str": "Hello", "color": 14593470}
-/

#eval fromJson? (α:=ColorfulText) <|
  .mkObj [("str", "Hello"), ("color", 0xDEADBE)]
/-
> Except.ok { str := "Hello", color := 14593470 }
-/
```

Note that Lean can clevery deriving instances for `ToJson` and `FromJson` classes; for example,
-/

/--
Example of (de)serialization of an enum type.
The values correspond to the constructors of `Lean.Declaration`
-/
inductive LeanDeclType where
| axiomDecl : LeanDeclType
| defnDecl : LeanDeclType
| thmDecl : LeanDeclType
| opaqueDecl : LeanDeclType
| quotDecl : LeanDeclType
| inductDecl : LeanDeclType
  deriving DecidableEq, Repr, ToJson, FromJson

/--
Example of a (de)serializable type for queries.
-/
structure DeclQuery where
  -- The name of the declarations which is to be searched.
  decl : Name
  -- The query can have an expected declaration type.
  expected? : Option LeanDeclType
  deriving DecidableEq, Repr, ToJson, FromJson

/-!
For example, a value of an enum type is represented by `Json.str` of its constructor name, and `a? : Option α` is the same as `a` if `a? = some a` and absent if `a? = none`:

```lean
#eval toJson <| DeclQuery.mk `True.intro (.some .thmDecl)
/-
> {"expected": "thmDecl", "decl": "True.intro"}
-/

#eval toJson <| DeclQuery.mk `Nat.succ .none
/-
> {"decl": "Nat.succ"}
-/
```
-/

/-!
### Writing a server RPC method

Recall that a server RPC method is defined in the `RequestM` monad context, and the result value is wrapped with `RequestTask`.

```lean
-- module: Lean.Server.Requests

abbrev RequestTask α := Task (Except RequestError α)
abbrev RequestM := ReaderT RequestContext <| EIO RequestError
```

`RequestContext` is the structure that carries the editor states:

```lean
-- module: Lean.Server.Requests

structure RequestContext where
  rpcSessions   : RBMap UInt64 (IO.Ref FileWorker.RpcSession) compare
  srcSearchPath : SearchPath
  doc           : FileWorker.EditableDocument
  hLog          : IO.FS.Stream
  hOut          : IO.FS.Stream
  initParams    : Lsp.InitializeParams
```

Especially, `RequestContext.doc` is the main part containing

* the environment constructed from the editor contents; and
* the parser state, including the cursor position.

Thus, most server RPC method begin with reading this field from `RequestContext`.
In `RequestM` monad, this is done by `RequestM.readDoc` function.

Given `doc : FileWorker.EditableDocument`, a function can get `Environment` associated with the editor state of `doc` as terms of type `Lean.Server.Snapshots.Snapshot` (`doc.cmdSnaps` more precisely).
In order to access them, one can make use of `bindWaitFindSnap` function instead of looking at the `FileWorker.EditableDocument.cmdSnaps` field directly:

```lean
-- module: Lean.Server.Requests

def bindWaitFindSnap (doc : EditableDocument) (p : Snapshot → Bool)
    (notFoundX : RequestM (RequestTask β))
    (x : Snapshot → RequestM (RequestTask β))
    (abortedX : RequestM (RequestTask β) := throwThe RequestError .fileChanged)
    : RequestM (RequestTask β)
```

One can write the RPC handler as the `x : Snapshot → RequestM (RequestTask β)` argument above.
For example, `Environment` is obtained by `Snapshot.env : Snapshot → Environment` function.
In fact, `snap : Snapshot` suffices to run some of the core monads; e.g. the core defines

```lean
-- module: Lean.Server.Requests

open Elab.Command in
def runCommandElabM (snap : Snapshot) (c : RequestT CommandElabM α) : RequestM α := do
  let rc ← readThe RequestContext
  match ← snap.runCommandElabM rc.doc.meta (c.run rc) with
  | .ok v => return v
  | .error e => throw e

def runCoreM (snap : Snapshot) (c : RequestT CoreM α) : RequestM α := do
  let rc ← readThe RequestContext
  match ← snap.runCoreM rc.doc.meta (c.run rc) with
  | .ok v => return v
  | .error e => throw e

open Elab.Term in
def runTermElabM (snap : Snapshot) (c : RequestT TermElabM α) : RequestM α := do
  let rc ← readThe RequestContext
  match ← snap.runTermElabM rc.doc.meta (c.run rc) with
  | .ok v => return v
  | .error e => throw e
```

As an example, we define a server RPC method that accepts `DeclQuery` defined above as the input and returns its declaration header, if any, as `ColorfulText`.
-/

open RequestM in
/--
An example server RPC module.
Given a query of type `query : DeclQuery`, the method tries to find a declaration with name `query.decl` in the current file environment.
If a declaration is found, it returns the header of the declaration, e.g. `def foo : True`, as a term of `ColorfulText` whose `color` is determined depending on the declaration type.
-/
def getColorfulDecl (query : DeclQuery) : RequestM (RequestTask ColorfulText) := do
  -- Get the current editor state
  let doc ← readDoc
  -- Preparing the "Not Found" error handler
  let notFoundX :=
    throwThe RequestError ⟨.unknownErrorCode, "Unexpected error"⟩
  -- The request handler body
  bindWaitFindSnap doc (fun _ => True) notFoundX fun snap => do
    -- Get the declaration information from the environment
    if let .some cinfo := snap.env.find? query.decl then
      let head : LeanDeclType → String := fun dt =>
        match query.expected? with
        | .none => ""
        | .some edt => if edt = dt then "◯" else "×"
      asTask <| pure <| match cinfo with
        | .axiomInfo  val => {
            str := head .axiomDecl ++ s!"axiom {val.name} : {val.type}"
            color := 0xFF0000
          }
        | .defnInfo   val => {
            str := head .defnDecl ++ s!"def {val.name} : {val.type}"
            color := 0x00FF00
          }
        | .thmInfo    val => {
            str := head .thmDecl ++ s!"theorem {val.name} : {val.type}"
            color := 0x0000FF
          }
        | .opaqueInfo val => {
            str := head .opaqueDecl ++ s!"opaque {val.name} : {val.type}"
            color := 0xFFFF00
          }
        | .quotInfo   val => {
            str := head .quotDecl ++ s!"quot {val.name} : {val.type}"
            color := 0xFF00FF
          }
        | .inductInfo val => {
            str := head .inductDecl ++ s!"inductive {val.name} : {val.type}"
            color := 0x00FFFF
          }
        | .ctorInfo   val => {
            str := s!"constructor {val.name} : {val.type}"
            color := 0x7F7F7F7F
          }
        | .recInfo    val => {
            str := s!"recursor {val.name} : {val.type}"
            color := 0x7F7F7F7F
          }
    else
      throwThe RequestError
        ⟨.invalidParams, s!"The declarations {query.decl} not found"⟩

/-!
### Registration of methods

Finally, we need to register a server RPC method to the Lean environment.
This is done by attaching `server_rpc_method` attribute.
-/

attribute [server_rpc_method] getColorfulDecl

/-!
The attribute calls `Lean.Server.registerRpcProcedure` with the method name.
It creates a wrapper function with name `(method name)._rpc_wrapped` and insert it into `userRpcProcedures` table in the environment with the method name as the key.
The wrapper function looks like as follows:

```lean
#print getColorfulDecl._rpc_wrapped
/-
> def getColorfulDecl._rpc_wrapped : Lean.Server.RpcProcedure :=
>   wrapRpcProcedure `getColorfulDecl DeclQuery ColorfulText getColorfulDecl
-/
```

Editors, such as VS Code, can interact with the Lean server using registered methods with their names as keys.
-/


/-!
## Use from widgets
-/

open Widget

@[widget]
def colorfulDeclWidget : UserWidgetDefinition where
  name := "Colorful Declaration"
  javascript := "
    import * as React from 'react'
    import {RpcContext, mapRpcError, useAsync} from '@leanprover/infoview'
    const e = React.createElement

    function numToColor(num) {
      const r = Number(num >> 16).toString(16).padStart(2,'0')
      const g = Number((num >> 8) & 255).toString(16).padStart(2,'0')
      const b = Number(num & 255).toString(16).padStart(2,'0')
      return '#' + r + g + b
    }

    function QueryResult({decl, expected}) {
      const rs = React.useContext(RpcContext)
      const st = useAsync(async () => {
        return await rs.call('getColorfulDecl', {decl, expected})
      }, [])
      const txt = st.value ? st.value.str : 'Unknown declaration'
      const col = st.value ? numToColor(st.value.color) : 'black'

      return st.state === 'resolved' ? e('p', {style: {color: col}}, txt)
        : st.state === 'rejected' ? e('p', null, mapRpcError(st.error).message)
        : e('p', null, 'Loading..')
    }

    export default function(props) {
      return e('div', null,
        e(QueryResult, {decl: props.decl, expected: props.expected}))
    }
  "

#widget colorfulDeclWidget (.mkObj [("decl", toJson `Nat.add_comm), ("expected", toJson LeanDeclType.thmDecl)])