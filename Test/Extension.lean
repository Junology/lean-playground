import Lean

import Std.Tactic.OpenPrivate

import LeanPlayground.Extension

open Lean Meta Elab

set_option autoImplicit false

universe u

/-- `lemma` means the same as `theorem`. It is used to denote "less important" theorems -/
syntax (name := myDef) declModifiers
  group("mydef " declId ppIndent(declSig) declVal) : command

section

open Command

export private expandDeclNamespace? in elabDeclaration

@[command_elab myDef]
def elabMyDef : CommandElab := fun stx => do
  match (← liftMacroM <| expandDeclNamespace? stx) with
  | some (ns, newStx) => do
    let ns := mkIdentFrom stx ns
    let newStx ← `(namespace $ns $(⟨newStx⟩) end $ns)
    withMacroExpansion stx newStx <| elabCommand newStx
  | none => do
    let decl     := stx[1]
    let declKind := decl.getKind
    dbg_trace "{decl}"
    dbg_trace "{declKind}"
    if declKind == ``Lean.Parser.Command.«axiom» then
      let modifiers ← elabModifiers stx[0]
      elabAxiom modifiers decl
    else if declKind == ``Lean.Parser.Command.«inductive» then
      let modifiers ← elabModifiers stx[0]
      elabInductive modifiers decl
    else if declKind == ``Lean.Parser.Command.classInductive then
      let modifiers ← elabModifiers stx[0]
      elabClassInductive modifiers decl
    else if declKind == ``Lean.Parser.Command.«structure» then
      let modifiers ← elabModifiers stx[0]
      elabStructure modifiers decl
    else if isDefLike decl then
      elabMutualDef #[stx]
    else
      throwError "unexpected declaration"

end

#print Lean.Elab.Command.elabDeclaration
#print Lean.Elab.PreDefinition
#print Lean.Elab.WF.packDomain

#print Lean.Elab.PreDefinition

variable {α : Type u}

@[myattr]
def myfun (x : Array α) (i : Fin x.size) : Array α :=
  let next := 2*i.1+1
  if h : next < x.size then
    have : x.size - next < x.size - i.1 := by omega
    myfun (x.swap i ⟨next,h⟩) ⟨next, (x.size_swap i ⟨next,h⟩).symm ▸ h⟩
  else
    x
termination_by x.size - i.1

#print myfun
attribute [instance] myfun._unary
#eval getMyExtensionDecls (m:=Lean.CoreM)
