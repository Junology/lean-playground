import Lean.Meta

open Lean Meta

initialize myExtension :
    SimpleScopedEnvExtension Name (Array Name) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun ns => ns.push
    initial := #[]
  }

@[inline] def getMyExtensionDecls {m : Type → Type} [Monad m] [MonadEnv m] : m (Array Name) := do
  return myExtension.getState (← getEnv)


syntax (name := myattr) "myattr" : attr

initialize registerBuiltinAttribute {
  name := `myattr
  descr := "Show all declarations that inherits an attribute 'myattr'."
  applicationTime := .afterTypeChecking
  add := fun declName _ _ => do
    MetaM.run' do myExtension.add declName
}
