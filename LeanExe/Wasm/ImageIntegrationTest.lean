import LeanExe.Wasm.Binary

namespace LeanExe.Wasm.ImageIntegrationTest

open LeanExe.IR
open LeanExe.Wasm

def emptyModule : Module :=
  { funcs := #[] }

def identityModule : Module :=
  { funcs :=
      #[{ sourceName := `identity
          exportName := some "identity"
          params := 1
          locals := 1
          body := .skip
          results := [.local 0] }] }

def nestedModule : Module :=
  { funcs :=
      #[{ sourceName := `choose
          exportName := some "choose"
          params := 1
          locals := 2
          body := .ite (.eqU64 (.local 0) (.u64 0))
            (.assign 1 (.u64 7))
            (.assign 1 (.u64 9))
          results := [.local 1] }] }

def imageBytesAgree (module_ : Module) : Bool :=
  Binary.CoreWasm.moduleBytes module_ == Binary.CoreWasm.moduleBytesFromImage module_

def imageRoundTrips (module_ : Module) : Bool :=
  let image := Binary.CoreWasm.moduleImage module_
  match Image.decodeModule (Image.encodeModule image) with
  | Except.ok decoded => decoded == image
  | Except.error _ => false

def publicEmitterAgrees (module_ : Module) : Bool :=
  let image := Binary.CoreWasm.moduleImage module_
  match Image.emitImage (Image.encodeModule image) with
  | Except.ok bytes => bytes == Binary.CoreWasm.moduleBytes module_
  | Except.error _ => false

#guard imageBytesAgree emptyModule
#guard imageBytesAgree identityModule
#guard imageBytesAgree nestedModule

#guard imageRoundTrips emptyModule
#guard imageRoundTrips identityModule
#guard imageRoundTrips nestedModule

#guard publicEmitterAgrees emptyModule
#guard publicEmitterAgrees identityModule
#guard publicEmitterAgrees nestedModule

end LeanExe.Wasm.ImageIntegrationTest
