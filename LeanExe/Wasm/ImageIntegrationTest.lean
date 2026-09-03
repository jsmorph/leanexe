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

def f64Module : Module :=
  { funcs :=
      #[{ sourceName := `f64Mul
          exportName := some "f64Mul"
          params := 2
          locals := 2
          body := .skip
          results := [.u64Bin .f64MulBits (.local 0) (.local 1)] }] }

def imageBytesAgree (module_ : Module) : Bool :=
  match Binary.CoreWasm.moduleBytesFromImage module_ with
  | Except.ok bytes => Binary.CoreWasm.legacyModuleBytes module_ == bytes
  | Except.error _ => false

def publicRouteAgrees (module_ : Module) : Bool :=
  Binary.CoreWasm.moduleBytes module_ == Binary.CoreWasm.legacyModuleBytes module_

def imageRoundTrips (module_ : Module) : Bool :=
  match Binary.CoreWasm.moduleImage module_ with
  | Except.error _ => false
  | Except.ok image =>
    match Image.decodeModule (Image.encodeModule image) with
    | Except.ok decoded => decoded == image
    | Except.error _ => false

def imageRejectsF64 (module_ : Module) : Bool :=
  match Binary.CoreWasm.moduleImage module_ with
  | Except.error error => error == Image.errorUnsupportedInstructionV2
  | Except.ok _ => false

def publicEmitterAgrees (module_ : Module) : Bool :=
  match Binary.CoreWasm.moduleImage module_ with
  | Except.error _ => false
  | Except.ok image =>
    match Image.emitImage (Image.encodeModule image) with
    | Except.ok bytes => bytes == Binary.CoreWasm.legacyModuleBytes module_
    | Except.error _ => false

#guard imageBytesAgree emptyModule
#guard imageBytesAgree identityModule
#guard imageBytesAgree nestedModule

#guard publicRouteAgrees emptyModule
#guard publicRouteAgrees identityModule
#guard publicRouteAgrees nestedModule

#guard imageRoundTrips emptyModule
#guard imageRoundTrips identityModule
#guard imageRoundTrips nestedModule

#guard imageRejectsF64 f64Module

#guard publicEmitterAgrees emptyModule
#guard publicEmitterAgrees identityModule
#guard publicEmitterAgrees nestedModule

end LeanExe.Wasm.ImageIntegrationTest
